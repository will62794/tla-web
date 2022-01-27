//
// TLA+ interpreter. 
//
// Contains logic for expression evaluation and initial/next generation.
//

// For debugging.
let depth = 0;

// Optionally enable tracing of evaluation.
const urlSearchParams = new URLSearchParams(window.location.search);
const params = Object.fromEntries(urlSearchParams.entries());
let enableEvalTracing = parseInt(params["debug"]);

// Simple assertion utility.
function assert(condition, message) {
    if (!condition) {
        throw new Error(message || 'Assertion failed');
    }
}
function evalLog(...msgArgs){
    if(enableEvalTracing){
        let indent = "(L"+depth+")" + ("|".repeat(depth * 2));
        let args = [indent].concat(msgArgs)
        console.log(...args);
    }
}

function cartesianProductOf() {
    return _.reduce(arguments, function(a, b) {
        return _.flatten(_.map(a, function(x) {
            return _.map(b, function(y) {
                return x.concat([y]);
            });
        }), true);
    }, [ [] ]);
}

function subsets(vals) {
	const powerset = [];
	generatePowerset([], 0);

	function generatePowerset(path, index) {
		powerset.push(path);
		for (let i = index; i < vals.length; i++) {
			generatePowerset([...path, vals[i]], i + 1);
		}
	}

	return powerset;
}

function hashState(stateObj){
    return objectHash.sha1(stateObj);
}

// 8 character prefix of the full hash.
function hashStateShort(stateObj){
    const shortHashPrefixLen = 6;
    return objectHash.sha1(stateObj).slice(0,shortHashPrefixLen);
}

// Rename primed variables to unprimed variables.
function renamePrimedVars(state){
    state = _.pickBy(state, (val,k,obj) => k.endsWith("'"));
    return _.mapKeys(state, (val,k,obj) => k.slice(0,k.length-1));
}

class TLAValue{
    constructor() {
    }
}

class NatValue extends TLAValue{
    constructor(n){
        super(n);
        this.val = n;
    }
    toString(){
        return this.val.toString();
    }
}

class StringValue extends TLAValue{
    constructor(s){
        super(s);
        this.val = s;
    }
    toString(){
        return this.val;
    }
}

/**
 * Extract all defintions and variable declarations from the given syntax tree
 * of a TLA+ module.
 */
function walkTree(tree){

    let cursor = tree.walk();
    
    // One level down from the top level tree node should contain the overall TLA module.
    cursor.gotoFirstChild();
    let node = cursor.currentNode();
    console.assert(node.type === "module")

    op_defs = {}
    var_decls = {}

    // Look for all variables and definitions defined in the module.
    let more = cursor.gotoFirstChild();
    while(more){
        more = cursor.gotoNextSibling();
        let node = cursor.currentNode();
        // console.log(node);
        // console.log("node type:");
        // console.log(node.type);
        // console.log("node text:");
        // console.log(node.text);
        // console.log("node id:");
        // console.log(node.id);

        if(node.type === "variable_declaration"){
            cursor.gotoFirstChild();
            cursor.gotoNextSibling();
            let var_ident = cursor.currentNode();
            cursor.gotoParent();
            // Save the variable declaration.
            var_decls[var_ident.text] = {"id": node.id}; 
        }

        if(node.type === "operator_definition"){
            // TODO: Consider iterating through 'named' children only?
            cursor.gotoFirstChild();

            // The definition identifier name.
            node = cursor.currentNode()
            console.log(node.text)
            console.log(node)
            console.log(cursor.currentFieldName());
            console.assert(node.type === "identifier");
            let opName = node.text;

            op_defs[opName] = {"name": opName, "args": [], "node": null};
            
            // Skip the 'def_eq' symbol ("==").
            cursor.gotoNextSibling();
            if(!cursor.currentNode().isNamed()){
                cursor.gotoNextSibling();
            }

            // n-ary operator. save all parameters.
            while(cursor.currentFieldName() === "parameter"){
                op_defs[opName]["args"].push(cursor.currentNode().text);
                cursor.gotoNextSibling();
                if(!cursor.currentNode().isNamed()){
                    cursor.gotoNextSibling();
                }
            }

            // Skip any intervening comment nodes.
            cursor.gotoNextSibling();
            while(cursor.currentNode().type === "comment"){
                cursor.gotoNextSibling();
                console.log(cursor.currentNode());
                console.log(cursor.currentNode().type);
                console.log(cursor.currentFieldName());
            }

            // We should now be at the definition node.
            // console.log(cursor.currentNode().text)
            let def = cursor.currentNode();
            // console.log("def type:", def.type);
            // console.log("def type:", def);

            // console.log(cursor.currentNode());
            // let var_ident = cursor.currentNode();
            cursor.gotoParent();
            // Save the variable declaration.
            // var_decls[var_ident.text] = {"id": node.id}; 
            op_defs[opName]["node"] = def;
            console.log("opDef:", op_defs[opName]);
        }
    }

    console.log("module declarations:",var_decls);
    console.log("module definitions:",op_defs);

    objs = {
        "var_decls": var_decls,
        "op_defs": op_defs
    }

    return objs;
}

function evalInitLand(lhs, rhs, contexts){
    // Evaluate left to right.
    evalLog("## LAND - LHS:", lhs.text, ", RHS: ", rhs.text);
    let lhsEval = _.flattenDeep(evalInitExpr(lhs, contexts));
    evalLog("lhsEval:", lhsEval);
    let rhsEval = lhsEval.map(lctx => {
        evalLog("rhs:", rhs.text);
        evalLog("lctx:", lctx);
        return evalInitExpr(rhs, lctx).map(ctx => {
            evalLog("ctx:", ctx);
            return Object.assign({}, ctx, {"val": (lctx["val"] && ctx["val"]), "state": ctx["state"]});
        })
    });
    return _.flattenDeep(rhsEval);
    
    // evalInitExpr(lhs, contexts)

    // // It's possible that the RHS forks the evaluation contexts further, so 
    // // we evaluate each current context, and compute its truth value against 
    // // all contexts returned by evaluation of the RHS.
    // let contextsOut = [];
    // for(const lctx of contextsLhs){
    //     let contextsRhs = evalInitExpr(rhs, [lctx]);
    //     contextsRhs = contextsRhs.map((rctx) => ({"val": lctx["val"] && rctx["val"], "state": rctx["state"]}));
    //     contextsOut = contextsOut.concat(contextsRhs);
    // }
    // return contextsOut;
}

function evalInitLor(lhs, rhs, contexts){
    // return {"val": false, "states": vars};
    evalLog("## LOR");
    evalLog("orig ctx:", contexts);
    // For all existing possible variable assignments split into
    // separate evaluation cases for left and right branch.
    let contextsLhs = evalInitExpr(lhs, contexts);
    evalLog("lhs contexts:",contextsLhs);
    let contextsRhs = evalInitExpr(rhs, contexts);
    return contextsLhs.concat(contextsRhs);
}

// Checks if a syntax tree node represents a primed variable.
function isPrimedVar(treeNode){
    if(treeNode.children.length < 2){
        return false;
    }
    let lhs = treeNode.children[0];
    let symbol = treeNode.children[1];
    return (treeNode.type === "bound_postfix_op" && 
            lhs.type === "identifier_ref" &&
            symbol.type === "prime");
}

function evalInitEq(lhs, rhs, contexts){
    // Deal with equality of variable on left hand side.
    let identName = lhs.text;

    // let isUnprimedVar = contexts[0]["state"].hasOwnProperty(varName) && !isPrimedVar(lhs);
    let isUnprimedVar = contexts["state"].hasOwnProperty(identName) && !isPrimedVar(lhs);
    // console.log("isUnprimedVar:", isUnprimedVar);

    if(isPrimedVar(lhs) || (isUnprimedVar && !ASSIGN_PRIMED)){
        // Update assignments for all current evaluation contexts.

        // If, in the current state assignment, the variable has not already
        // been assigned a value, then assign it.If it has already been assigned,
        // then check for equality.
        // Variable already assigned in this context. So, check for equality.
        if(contexts["state"].hasOwnProperty(identName) && contexts["state"][identName] !== null){
            evalLog("Variable '" + identName + "' already assigned in ctx:",  contexts);
            let rhsVals = evalInitExpr(rhs, contexts);
            console.assert(rhsVals.length === 1);
            let rhsVal = rhsVals[0]["val"]
            evalLog("rhsVal:", rhsVal);
            let boolVal = (contexts["state"][identName] === rhsVal)
            evalLog("boolVal:", boolVal);
            return Object.assign({}, contexts, {"val": boolVal})
            return [{"val": boolVal, "state": contexts["state"]}]; 
        }

        // Variable not already assigned. So, update variable assignment as necessary.
        let stateUpdated = _.mapValues(contexts["state"], (val,key,obj) => {
            if(key === identName){
                evalLog("Variable (" + identName + ") not already assigned in ctx:",  contexts);
                let rhsVals = evalInitExpr(rhs, _.cloneDeep(contexts));
                console.assert(rhsVals.length === 1);
                let rhsVal = rhsVals[0]["val"];
                evalLog("Variable (" + identName + ") getting value:",  rhsVal);
                return (val === null) ? rhsVal : val;
            } 
            return val;
        })
        return [Object.assign({}, contexts, {"val": true, "state": stateUpdated})];
        // return [{"val": true, "state": stateUpdated}];
        // return [_.update(contexts, "val", () => boolVal)];

    } else{
        evalLog(`Checking for equality of ident '${identName}' with '${rhs.text}'.`, contexts);
        
        // Evaluate left and right hand side.
        let lhsVals = evalInitExpr(lhs, _.cloneDeep(contexts));
        console.assert(lhsVals.length === 1);
        let lhsVal = lhsVals[0]["val"];
        // console.log("Checking for, lhsVal", lhsVal);

        let rhsVals = evalInitExpr(rhs, _.cloneDeep(contexts));
        console.assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        // console.log("Checking for, rhsVal", rhsVal);

        // Check equality.
        const boolVal = _.isEqual(lhsVal, rhsVal);
        // console.log("Checking for, boolVal:", boolVal);

        // Return context with updated value.
        return [Object.assign({}, contexts, {"val": boolVal})];
    }
}

// 'vars' is a list of possible partial state assignments known up to this point.
function evalInitBoundInfix(node, contexts){
    evalLog("evalInitBoundInfix:", node);

    // lhs.
    let lhs = node.children[0];
    // symbol.
    let symbol = node.children[1];
    // console.log("symbol:", node.children[1].type);
    // rhs
    let rhs = node.children[2];

    // Multiplication
    if(symbol.type === "mul"){
        evalLog("mul lhs:", lhs, lhs.text);
        let mulLhsVal = evalInitExpr(lhs, contexts);
        evalLog("mul lhs val:", mulLhsVal);
        let lhsVal = mulLhsVal[0]["val"];
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        let outVal = lhsVal * rhsVal;
        // console.log("mul overall val:", outVal);
        return [Object.assign({}, contexts, {"val": outVal})];
    }

    // Plus.
    if(symbol.type === "plus"){
        evalLog("plus lhs:", lhs, lhs.text);
        let plusLhsVal = evalInitExpr(lhs, contexts);
        evalLog("plus lhs val:", plusLhsVal);
        let lhsVal = plusLhsVal[0]["val"];
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        let outVal = lhsVal + rhsVal;
        return [Object.assign({}, contexts, {"val": outVal})];
    }

    // Greater than.
    if(symbol.type === "gt"){
        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        let outVal = lhsVal > rhsVal;
        return [Object.assign({}, contexts, {"val": outVal})];
    }

    if(symbol.type === "geq"){
        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        let outVal = lhsVal >= rhsVal;
        return [Object.assign({}, contexts, {"val": outVal})];
    }

    // Disjunction.
    if(symbol.type === "lor"){
        return evalInitLor(lhs, rhs, contexts);
    }

    if(symbol.type === "land"){
        return evalInitLand(lhs, rhs, contexts);
    }

    // Equality.
    if(symbol.type ==="eq"){
        // console.log("bound_infix_op, symbol 'eq', ctx:", JSON.stringify(contexts));
        evalLog("bound_infix_op -> (eq), ctx:", contexts);
        return evalInitEq(lhs, rhs, contexts);
    } 

    // Inequality.
    if(symbol.type ==="neq"){
        // console.log("bound_infix_op, symbol 'neq', ctx:", JSON.stringify(contexts));
        evalLog("bound_infix_op -> (neq), ctx:", contexts);
        
        let lident = lhs.text;
        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        // console.log("Checking for inequality with var:", varName);
        let rhsVals = evalInitExpr(rhs, contexts);
        console.assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        let boolVal = !_.isEqual(lhsVal, rhsVal);
        // console.log("inequality lhsVal:", lhsVal);
        // console.log("inequality rhsVal:", rhsVal);
        evalLog("inequality boolVal:", boolVal);
        // Return context with updated value.
        return [Object.assign({}, contexts, {"val": boolVal})];
    } 

    // Set membership.
    if(symbol.type ==="in"){
        // console.log("bound_infix_op, symbol 'in', ctx:", contexts);
        evalLog("bound_infix_op, symbol 'in', ctx:", contexts);
        let lhs = node.namedChildren[0];
        let rhs = node.namedChildren[2];

        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        evalLog("setin lhsval:", lhsVal, lhs.text, contexts);

        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        evalLog("setin rhsval:", rhsVal, rhs.text, contexts);

        evalLog("setin lhs in rhs:", rhsVal.includes(lhsVal));
        return [Object.assign({}, contexts, {"val": rhsVal.includes(lhsVal)})]
    } 
    
    // Set intersection.
    if(symbol.type ==="cap"){
        evalLog("bound_infix_op, symbol 'cap'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        evalLog("cap lhs:", lhsVal);
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        evalLog("cap rhs:", rhsVal);
        let capVal = _.intersectionWith(lhsVal, rhsVal, _.isEqual);
        return [Object.assign({}, contexts, {"val": capVal})];
    } 

    // Set union.
    if(symbol.type ==="cup"){
        // console.log("bound_infix_op, symbol 'cup'");
        evalLog("bound_infix_op, symbol 'cup'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        evalLog(lhs);
        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        evalLog("cup lhs:", lhsVal);
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        evalLog("cup rhs:", lhsVal);
        return [Object.assign({}, contexts, {"val": _.uniq(lhsVal.concat(rhsVal))})];
    }   

    // Set minus.
    if(symbol.type ==="setminus"){
        // console.log("bound_infix_op, symbol 'setminus'");
        evalLog("bound_infix_op, symbol 'setminus'");
        // TODO: Will need to figure out a more principled approach to object equality.
        console.log(lhs);
        let lhsVal = evalInitExpr(lhs, contexts)[0]["val"];
        console.log("setminus lhs:", lhsVal);
        let rhsVal = evalInitExpr(rhs, contexts)[0]["val"];
        console.log("setminus rhs:", lhsVal);
        return [Object.assign({}, contexts, {"val": _.difference(lhsVal,rhsVal)})];
    }  
}

function evalInitDisjList(parent, disjs, contexts){
    console.log("evalInit: disjunction list!");

    // Split into separate evaluation cases for each disjunct.
    return _.flattenDeep(disjs.map(disj => evalInitExpr(disj, contexts)));

    // let newContexts = disjs.map(disj => evalInitExpr(disj, contexts));
    // console.log("newContexts:", newContexts);
    // return _.flatten(newContexts);

    // let contextsLhs = evalInitExpr(lhs, contexts);
    // let contextsRhs = evalInitExpr(rhs, contexts);
    // return contextsLhs.concat(contextsRhs);
}

function evalInitConjList(parent, conjs, contexts){
    evalLog("evalInitConjList -> ctx:", contexts);

    // Initialize boolean value if needed.
    if(contexts["val"]===null){
        contexts["val"]=true;
    }
    return conjs.reduce((prevRes,currConj) => {
        return _.flattenDeep(prevRes.map(ctx => {
            return evalInitExpr(currConj, ctx).map(cb => Object.assign({}, cb, {"val": cb["val"] && ctx["val"]}));
        }));
    }, [contexts]);
}

function evalInitIdentifierRef(node, contexts){
    let ident_name = node.text;
    evalLog(`evalInitIdentifierRef, '${node.text}' context:`, contexts);

    // If this identifier refers to a variable, return the value bound
    // to that variable in the current context.
    if(contexts["state"].hasOwnProperty(ident_name)){
        evalLog("variable identifier: ", ident_name);
        let var_val = contexts["state"][ident_name];
        evalLog("var ident context:", contexts["state"], var_val);
        // return [{"val": var_val, "state": contexts["state"]}];
        return [Object.assign({}, contexts, {"val": var_val})];
    }

    // See if the identifier is bound to a value in the current context.
    // If so, return the value it is bound to.
    if(contexts.hasOwnProperty("quant_bound") && contexts["quant_bound"].hasOwnProperty(ident_name)){
        let bound_val = contexts["quant_bound"][ident_name];
        evalLog("bound_val", bound_val);
        return [Object.assign({}, contexts, {"val": bound_val})];
        // return [{"val": bound_val, "state": contexts["state"]}];
    }

    // See if this identifier is a definition in the spec.
    if(contexts["defns"].hasOwnProperty(ident_name)){
        // Evaluate the definition in the current context.
        // TODO: Consider defs that are n-ary operators.
        let defNode = contexts["defns"][ident_name]["node"];
        // return undefined;
        return evalInitExpr(defNode, contexts);
    }

    // TODO: Consider case of being undefined.
}


class Context{
    constructor(val, state, defns, quant_bound) {
        this.val = val;
        this.state = state;
        this.defns = defns;
        this.quant_bound = quant_bound;
    }

    show(){
        return this.defns;
    }
}

/**
 * Evaluate a TLC expression.
 * 
 * Note that evaluation of a TLC expression is not only about producing a single
 * value. In the simple case, expression evaluation simply takes in an
 * expression and returns a single TLC value. When we are evaluating an
 * expression in the form of an initial state or next state predicate, however,
 * things are more involved. 
 * 
 * That is, when evaluating an initial/next state predicate for generating
 * states, the expression returns both a boolean value (TRUE/FALSE) as well as
 * an assignment of values to variables. In the context of initial state
 * generation, this is an assignment of values to all variables x1,...,xn
 * declared in a specification. In the context of next state generation, though,
 * this is an assignment of values to all variables x1,...,xn,x1',...,xn' i.e.
 * the "current" state variables and the "next"/"primed" copy of the state
 * variables. More precisely, predicate evaluation of this variety may actually
 * produce not only a single return value, but a set of return values. That is,
 * one for each potential "branch" of the evaluation, corresponding to possible
 * disjunctions that appear in the predicate. For example, the initial state
 * predicate x = 0 \/ x = 1 will produce two possible results, both of which
 * evaluate to TRUE and which assign the values of 0 and 1, respectively, to the
 * variable 'x'.
 * 
 * To handle this type of evaluation strategy, we allow expression evaluation to
 * take in a current 'context', which consists of several items for tracking
 * data needed during evaluation:
 * 
 * Context : {
 *   val: TLCValue
 *      The result value of this expression, or 'null' if no result has been
 *      computed yet.
 *   
 *   state: string -> TLCValue
 *      Represents the current assignment of values to variables in an
 *      in-progress expression evaluation. 
 * 
 *   defns: string -> TLCSyntaxNode
 *      Global definitions that exist in the specification, stored as mapping from
 *      definition names to their syntax tree node.
 *   
 *   quant_bound: string -> TLCValue
 *      Currently bound identifiers in the in-progress expression evaluation,
 *      stored as a mapping from identifier names to their TLC values.
 * }
 * 
 * Expression evaluation can return a list (i.e set) of these context objects,
 * one for each potential evaluation branch of a given expression. In each
 * returned context, the assignment of values to variables, 'state', will
 * potentially be updated, as will the 'val' output value. The bound quantifiers
 * may also be updated.
 *
 * In our implementation, though, we have each evaluation handler function take
 * in a single context object, and return potentially many contexts. This makes
 * it easier to implement each evaluation handler function, by focusing just on
 * how to evaluate an expression given a single context, and either update it,
 * or fork it into multiple new sub-contexts.
 * 
 * @param {TLASyntaxNode} node: TLA+ tree sitter syntax node representing the expression to evaluate.
 * @param {Context} ctx: a 'Context' instance under which to evaluate the given expression.
 * @returns 
 */
function evalInitExpr(node, ctx){
    // TODO: Enable this after argument conversion.
    // assert(ctx instanceof Context);

    // console.log("$$ evalInitExpr, node: ", node, node.text);
    evalLog("evalInitExpr -> ("+ node.type + ") '" + node.text + "'");

    // [<lExpr> EXCEPT ![<updateExpr>] = <rExpr>]
    if(node.type === "except"){
        evalLog("EXCEPT node, ctx:", ctx);
        let lExpr = node.namedChildren[0];
        let updateExpr = node.namedChildren[1];
        let rExpr = node.namedChildren[2];

        // This value should be a function.
        evalLog("lExpr:",lExpr); 
        let lExprVal = evalInitExpr(lExpr, ctx);
        evalLog("lexprval:", lExprVal);
        // console.assert(lExprVal.type === "function");
        let fnVal = lExprVal[0]["val"];
        evalLog("fnVal:",fnVal);

        evalLog(updateExpr);
        let updateExprVal = evalInitExpr(updateExpr, ctx)[0]["val"];
        evalLog("updateExprVal:", updateExprVal);

        let rExprVal = evalInitExpr(rExpr, ctx)[0]["val"];
        evalLog("rExprVal:", rExprVal);
        fnVal[updateExprVal] = rExprVal;

        return [Object.assign({}, ctx, {"val": _.cloneDeep(fnVal)})];

        throw Error("Evaluation of 'except' node type not implemented.");

    }
    if(node.type === "function_evaluation"){
        evalLog("function_evaluation");
        let fnVal = evalInitExpr(node.namedChildren[0], ctx)[0]["val"];
        // console.log("fnArg node: ", node.namedChildren[1]);
        let fnArgVal = evalInitExpr(node.namedChildren[1], ctx);
        // console.log("fnArgVal:", fnArgVal);
        let fnArg = evalInitExpr(node.namedChildren[1], ctx)[0]["val"];
        evalLog("fneval:", fnVal, fnArg);
        return [Object.assign({}, ctx, {"val": fnVal[fnArg]})];
    }


    if(node.type === "comment"){
        // TOOD: Handle properly.
    }
    if(node === undefined){
        return [{"val": false, "state": {}}];
    }
    if(node.type === "conj_list"){
        return evalInitConjList(node, node.children, ctx);
    }  
    if(node.type === "disj_list"){
        return evalInitDisjList(node, node.children, ctx);
    }  
    if(node.type === "conj_item"){
        conj_item_node = node.children[1];
        return evalInitExpr(conj_item_node, ctx);
    }
    if(node.type === "disj_item"){
        disj_item_node = node.children[1];
        return evalInitExpr(disj_item_node, ctx);
    }

    if(node.type === "bound_op"){
        let opName = node.namedChildren[0].text;
        let argExpr = node.namedChildren[1];
        evalLog("bound_op:", opName);
        evalLog("bound_op context:",ctx);

        let argExprVal = evalInitExpr(argExpr, ctx)[0]["val"]
        // Built in bound ops.
        if(opName == "Cardinality"){
            evalLog("Cardinality val:", argExpr.text, argExprVal.length);
            return [Object.assign({}, ctx, {"val": argExprVal.length})];
        }

        // Check for the bound op in the set of known definitions.
        if(ctx["defns"].hasOwnProperty(opName)){
            let opDefNode = ctx["defns"][opName]["node"];
            let opDefObj = ctx["defns"][opName];
            let opArgs = opDefObj["args"];
            evalLog("defns", node);
            evalLog("opDefObj", opDefObj);

            // n-ary operator.
            // if(node.namedChildren.length > 1){
            if(opArgs.length > 1){
                // Evaluate each operator argument.
                let opArgVals = _.flatten(node.namedChildren.slice(1).map(c => evalInitExpr(c, ctx)));
                evalLog("opArgVals:", opArgVals);

                // Then, evaluate the operator defininition with these argument values bound
                // to the appropriate names.
                let opEvalContext = _.cloneDeep(ctx);
                if(!opEvalContext.hasOwnProperty("quant_bound")){
                    opEvalContext["quant_bound"] = {};
                }

                evalLog("opDefNode", opDefNode);
                // for(var i=0;i<opArgVals.length;i++){
                for(var i=0;i<opArgs.length;i++){
                        // The parameter name in the operator definition.
                    let paramName = opArgs[i];
                    // console.log("paramName:", paramName);
                    opEvalContext["quant_bound"][paramName] = opArgVals[i]["val"];
                }
                evalLog("opEvalContext:", opEvalContext);
                return evalInitExpr(opDefNode, opEvalContext);
            }
        }

    }

    if(node.type === "bound_infix_op"){
        // evalLog(node.type + ", ", node.text, ", ctx:", JSON.stringify(contexts));
        return evalInitBoundInfix(node, ctx);
    }

    if(node.type === "bound_prefix_op"){
        let symbol = node.children[0];
        let rhs = node.children[1];
        evalLog(node.type, ", ", node.text, `, prefix symbol: '${symbol.type}' `, "ctx:", ctx);
        if(symbol.type === "powerset"){
            evalLog("POWERSET op");
            evalLog(rhs);
            let rhsVal = evalInitExpr(rhs, ctx);
            evalLog("rhsVal: ", rhsVal);
            rhsVal = rhsVal[0]["val"];
            let powersetRhs = subsets(rhsVal);
            evalLog("powerset:",powersetRhs);
            // return [Object.assign({}, ctx, {"val":powersetRhs})];
            return [{"val": powersetRhs, "state": {}}];
        }
        if(symbol.type === "negative"){
            let rhsVal = evalInitExpr(rhs, ctx);
            rhsVal = rhsVal[0]["val"];
            return [{"val": -rhsVal, "state": {}}];
        }   

        if(symbol.type === "lnot"){
            let rhsVal = evalInitExpr(rhs, ctx);
            rhsVal = rhsVal[0]["val"];
            return [{"val": !rhsVal, "state": {}}];
        }   
    }

    // TODO: Finish this after implementing 'except' node type handling.
    if(node.type === "bounded_quantification"){
        evalLog("bounded_quantification");
        let quantifier = node.namedChildren[0];

        // Extract all quantifier bounds/domains.
        let currInd = 1;
        quantBounds = [];
        while(node.namedChildren[currInd].type === "quantifier_bound"){
            quantBounds.push(node.namedChildren[currInd]);
            currInd += 1;
        }

        // The quantified expression.
        let quant_expr = node.namedChildren[currInd];
        evalLog("quant bounds:", quantBounds);
        evalLog("quant expr:", quant_expr);

        let quantDomains = quantBounds.map(qbound =>{
            expr = evalInitExpr(qbound.children[2], ctx);
            let domain = expr[0]["val"];
            return domain;
        });
        let quantIdents = quantBounds.map(qbound => qbound.children[0].text);

        // Iterate over the product of all quantified domains and evaluate
        // the quantified expression with the appropriately bound values.
        let quantDomainTuples = cartesianProductOf(...quantDomains);
        evalLog("quantDomain tuples:", quantDomainTuples);
        if(quantDomainTuples.length === 0){
            return [{"val": false, "state": {}}];
        }

        return _.flattenDeep(quantDomainTuples.map(qtup => {
            let boundContext = _.cloneDeep(ctx);
            // Bound values to quantified variables.
            if(!boundContext.hasOwnProperty("quant_bound")){
                boundContext["quant_bound"] = {};
            }
            for(var qk = 0;qk<quantIdents.length;qk++){
                boundContext["quant_bound"][quantIdents[qk]] = qtup[qk];
            }
            evalLog("quantDomain val:", qtup);
            evalLog("boundContext:", boundContext);
            let ret = evalInitExpr(quant_expr, _.cloneDeep(boundContext));
            return ret;
        }));
    }

    if(node.type === "identifier_ref"){
        return evalInitIdentifierRef(node, ctx);
    }

    if(node.type === "nat_number"){
        // console.log(node.type, node.text);
        return [{"val": parseInt(node.text), "state": {}}];
        // return [{"val": new NatValue(parseInt(node.text)), "state": {}}];
    }

    if(node.type === "boolean"){
        evalLog(node.type, node.text);
        let boolVal = node.text === "TRUE" ? true : false;
        return [{"val": boolVal, "state": {}}];
    }

    if(node.type === "string"){
        evalLog("string node", node.text);
        // Remove the quotes.
        let rawStr = node.text.substring(1,node.text.length-1);
        return [{"val": rawStr, "state": {}}];
        // return [{"val": new StringValue(rawStr), "state": {}}];
    }

    if(node.type === "if_then_else"){
        let cond = node.namedChildren[0];
        let thenNode = node.namedChildren[1];
        let elseNode = node.namedChildren[2];

        let condVal = evalInitExpr(cond, _.cloneDeep(ctx))[0]["val"];
        if(condVal){
            let thenVal = evalInitExpr(thenNode, _.cloneDeep(ctx));
            evalLog("thenVal", thenVal, thenNode.text);
            return thenVal;
        } else{
            let elseVal = evalInitExpr(elseNode, _.cloneDeep(ctx));
            evalLog("elseVal", elseVal, elseNode.text, ctx);
            return elseVal;
        }
    }

    // {<single_quantifier_bound> : <expr>}
    // {i \in A : <expr>}
    if(node.type === "set_filter"){
        evalLog("SET_FILTER");
        // Extract the left and right side of the ":" of the set filter.
        let singleQuantBound = node.namedChildren[0];
        let rhsFilter = node.namedChildren[1];

        // Evaluate the quantified domain.
        console.assert(singleQuantBound.type === "single_quantifier_bound");
        evalLog("singleQuantBound:", singleQuantBound, singleQuantBound.text);
        let ident = singleQuantBound.namedChildren[0].text;
        let domainExpr = singleQuantBound.namedChildren[2];
        evalLog(domainExpr);
        let domainExprVal = evalInitExpr(domainExpr, ctx)[0]["val"];
        
        evalLog("domainExprVal:", domainExprVal);

        // Return all values in domain for which the set filter evaluates to true.
        let filteredVals = domainExprVal.filter(exprVal => {
            // Evaluate rhs in context of the bound value and check its truth value.
            let boundContext = _.cloneDeep(ctx);
            if(!boundContext.hasOwnProperty("quant_bound")){
                boundContext["quant_bound"] = {};
            }
            boundContext["quant_bound"][ident] = exprVal;
            evalLog("rhsFilterVal:", evalInitExpr(rhsFilter, boundContext));
            let rhsFilterVal = evalInitExpr(rhsFilter, boundContext)[0]["val"];
            return rhsFilterVal;
        });
        evalLog("domainExprVal filtered:", filteredVals);
        return [Object.assign({}, ctx, {"val": filteredVals})];
    }


    // TODO: Re-examine whether this implementation is correct.
    if(node.type ==="finite_set_literal"){
        // TODO: Check the computation below for correctness.

        // Remove the outer braces, "{" and "}"
        let innerChildren = node.children.slice(1,node.children.length-1);
        // Remove commas and then evaluate each set element.
        let ret = innerChildren.filter(child => child.type !== ",")
        ret = ret.map(child => {
            // TODO: For now assume set elements don't fork evaluation context.
            let r = evalInitExpr(child, ctx);
            console.assert(r.length === 1);
            return r[0]["val"];
        });
        ret = _.flatten(ret);
        // console.log(ret);
        return [{"val": ret, "state": ctx["state"]}];

        // let ret = node.children.map(child => evalInitExpr(child, ctx));
        // console.log(_.flatten(ret));
        return ret;
    }

    if(node.type === "record_value"){
        evalLog("RECVAL", node);
        let rec = node.namedChildren[0];
        let recField = node.namedChildren[1].text;

        let recVal = evalInitExpr(rec, ctx)[0]["val"];
        evalLog("recVal", recVal);
        evalLog("recField", recField);
        let fieldVal = recVal[recField];
        return [{"val": fieldVal, "state": ctx["state"]}];

    }


    // [<identifier> |-> <expr>, <identifier> |-> <expr>, ...]
    // "|->" is of type 'all_map_to'.
    if(node.type === "record_literal"){
        evalLog("RECLIT", node);
        let record_obj = {}
        for(var i=0;i<node.namedChildren.length;i+=3){
            let ident = node.namedChildren[i]
            let exprNode = node.namedChildren[i+2]

            let identName = ident.text;
            let exprVal = evalInitExpr(exprNode, ctx);
            record_obj[identName] = exprVal[0]["val"];
        }
        evalLog("RECOBJ", record_obj);
        return [{"val": record_obj, "state": ctx["state"]}];
    }


    // "[" <quantifier_bound> "|->" <expr> "]"
    if(node.type === "function_literal"){
        // lbracket = node.children[0]
        // rbracket = node.children[4];
        evalLog("function_literal: '" +  node.text + "'");

        let quant_bound = node.children[1];
        let all_map_to = node.children[2];
        let fexpr = node.children[3];

        console.assert(all_map_to.type === "all_map_to");

        // Handle the quantifier bound:
        // <identifier> \in <expr>
        quant_ident = quant_bound.children[0];
        quant_expr = evalInitExpr(quant_bound.children[2], ctx);
        evalLog("function_literal quant_expr:", quant_expr);
        evalLog(quant_ident.type);
        evalLog(quant_expr.type);

        // Evaluate the quantified expression for each element in the 
        // quantifier domain.
        // TODO: For now assume that quantifier domain doesn't fork evaluation.
        let domain = quant_expr[0]["val"];
        let fnVal = {}; //_.fromPairs(domain.map(x => [x,null]));
        for(const v of domain){
            // Evaluate the expression in a context with the the current domain 
            // value bound to the identifier.
            // let boundContext = {"val": ctx["val"], "state": ctx["state"]};
            
            let boundContext = _.cloneDeep(ctx);
            if(!boundContext.hasOwnProperty("quant_bound")){
                boundContext["quant_bound"] = {};
            }
            boundContext["quant_bound"][quant_ident.text] = v;
            evalLog("function_literal boundCtx:", boundContext);
            // TODO: Handle bound quantifier values during evaluation.
            let vals = evalInitExpr(fexpr, boundContext);
            evalLog("fexpr vals:", vals);
            console.assert(vals.length === 1);
            fnVal[v] = vals[0]["val"];
        }
        evalLog("fnVal:", fnVal);
        return [{"val":fnVal, "state":{}}];
    }
}

/**
 * Generates all possible initial states given the syntax tree node for the
 * initial state predicate and an object 'vars' which contains exactly the
 * specification's state variables as keys.
 */
function getInitStates(initDef, vars, defns){
    // TODO: Pass this variable value as an argument to the evaluation functions.
    ASSIGN_PRIMED = false;

    // Values of each state variable. Initially empty.
    init_var_vals = {};
    for(v in vars){
        init_var_vals[v] = null;
    }

    // We refer to a 'context' as the context for a single evaluation
    // branch, which contains a computed value along with a list of 
    // generated states.
    let initCtx = new Context(null, init_var_vals, defns, {});
    console.log("INITCTX:", initCtx);
    console.log("INITCTX:", initCtx instanceof Context);
    let init_ctx = {"val": null, "state": init_var_vals, "defns": defns};
    // let ret_ctxs = evalInitExpr(initDef, [init_ctx]);
    // let ret_ctxs = evalInitExpr(initDef, init_ctx);
    let ret_ctxs = evalInitExpr(initDef, initCtx);
    if(ret_ctxs === undefined){
        console.error("Set of generated initial states is 'undefined'.");
    }
    console.log("Possible initial state assignments:");
    for(const ctx of ret_ctxs){
        console.log(ctx);
    }
    return ret_ctxs;
}

/**
 * Generates all possible successor states from a given state and the syntax
 * tree node for the definition of the next state predicate.
 */
function getNextStates(nextDef, currStateVars, defns){
    // TODO: Pass this variable value as an argument to the evaluation functions.
    ASSIGN_PRIMED = true;
    let origVars = Object.keys(currStateVars);

    for(var k in currStateVars){
        let primedVar = k + "'";
        currStateVars[primedVar] = null;
    }
    console.log("currStateVars:", currStateVars);
    // let init_ctxs = [{"val": null, "state": currStateVars}]
    let init_ctx = {"val": null, "state": currStateVars, "defns": defns};
    // let ret = evalNextExpr(nextDef, init_ctxs);
    // console.log("nextDef:", nextDef);
    let ret = evalInitExpr(nextDef, init_ctx);
    console.log("getNextStates ret:", ret);

    // Filter out disabled transitions.
    ret = ret.filter(c => c["val"] === true);

    // Filter out transitions that do not modify the state.
    return ret.filter(c => {
        return !_.every(origVars, (v) => _.isEqual(c["state"][v], c["state"][v+"'"]));
    });
}

// TODO: Consider reconciling this with 'getInitStates' function.
function computeInitStates(tree){
    objs = walkTree(tree);

    let vars = objs["var_decls"];
    let defns = objs["op_defs"];

    let initDef = defns["Init"];
    console.log("<<<<< INIT >>>>>");
    console.log(initDef);
    console.log("initDef.childCount: ", initDef["node"].childCount);
    console.log("initDef.type: ", initDef["node"].type);

    let initStates = getInitStates(initDef["node"], vars, defns);
    // Keep only the valid states.
    initStates = initStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);
    return initStates;
}

// TODO: Consider reconciling this with 'getNextStates' function.
function computeNextStates(tree, initStates){
    objs = walkTree(tree);

    let vars = objs["var_decls"];
    let defns = objs["op_defs"];

    let nextDef = defns["Next"];
    console.log(defns);
    console.log("<<<< NEXT >>>>");
    console.log(nextDef);
    console.log("nextDef.childCount: ", nextDef["node"].childCount);
    console.log("nextDef.type: ", nextDef["node"].type);

    let allNext = []
    for(const istate of initStates){
        let currState = _.cloneDeep(istate);
        console.log("###### Computing next states from state: ", currState);
        let ret = getNextStates(nextDef["node"], currState, defns);
        allNext = allNext.concat(ret);
    }
    return allNext;
}

function computeReachableStates(tree){
    objs = walkTree(tree);

    let vars = objs["var_decls"];
    let defns = objs["op_defs"];

    let initDef = defns["Init"];
    let nextDef = defns["Next"];

    // Compute initial states and keep only the valid ones.
    let initStates = getInitStates(initDef["node"], vars, defns);
    initStates = initStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);

    let stateQueue = initStates;
    let seenStatesHashSet = new Set(); 
    let reachableStates = [];
    while(stateQueue.length > 0){
        let currState = stateQueue.pop();
        console.log(currState);
        let currStateHash = hashState(currState);
        console.log(currStateHash);

        // If we've already seen this state, we don't need to explore it.
        if(seenStatesHashSet.has(currStateHash)){
            continue;
        }

        // Mark the state as seen and record it as reachable.
        seenStatesHashSet.add(currStateHash);
        reachableStates.push(currState);

        // Compute next states reachable from the current state, and add
        // them to the state queue.
        let currStateArg = _.cloneDeep(currState);
        let nextStates = getNextStates(nextDef["node"], currStateArg, defns)
                            .map(c => c["state"])
                            .map(renamePrimedVars);
        // console.log("nextStates:", nextStates);
        // console.log("reachableStates:", reachableStates);
        stateQueue = stateQueue.concat(nextStates);
    }
    return reachableStates;
}

function generateStates(tree){
    console.log("Extracting definitions/declarations from syntax tree.");
    objs = walkTree(tree);

    let vars = objs["var_decls"];
    let defns = objs["op_defs"];

    let initDef = defns["Init"];
    console.log("<<<<< INIT >>>>>");
    console.log(initDef);
    console.log("initDef.childCount: ", initDef.childCount);
    console.log("initDef.type: ", initDef.type);

    let initStates = getInitStates(initDef, vars, defns);
    // Keep only the valid states.
    initStates = initStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);
    console.log("initial states:", initStates);

    console.log("INITIAL STATES:");
    for(const state of initStates){
        console.log(state);
    }

    let nextDef = defns["Next"];
    console.log(defns);
    console.log("<<<< NEXT >>>>");
    console.log(nextDef);
    console.log("nextDef.childCount: ", nextDef.childCount);
    console.log("nextDef.type: ", nextDef.type);

    // // let currState = initStates[0]["state"];
    let allNext = []
    for(const istate of initStates){
        let currState = _.cloneDeep(istate);
        console.log("###### Computing next states from state: ", currState);
        let ret = getNextStates(nextDef, currState, defns);
        // console.log(ret);
        allNext = allNext.concat(ret);
    }

    console.log("NEXT STATES:");
    for(const ctx of allNext){
        console.log(ctx);
    }
    return {"initStates": initStates, "nextStates": allNext};
}



//
// For debugging/tracing expression evaluation.
//

let origEvalInitExpr = evalInitExpr;
evalInitExpr = function(...args){
    depth += 1;
    let ret = origEvalInitExpr(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}

let origEvalInitBoundInfix = evalInitBoundInfix;
evalInitBoundInfix = function(...args){
    depth += 1;
    let ret = origEvalInitBoundInfix(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}

let origEvalInitConjList = evalInitConjList;
evalInitConjList = function(...args){
    depth += 1;
    let ret = origEvalInitConjList(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}
