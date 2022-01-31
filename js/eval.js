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
            console.log(node.text, node)
            // console.log(cursor.currentFieldName());
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

/**
 * Defines an evaluation context structure for evaluating TLC expressions and
 * initial/next state generation.
 */
class Context{
    constructor(val, state, defns, quant_bound) {

        // @type: TLAValue
        // The result value of a TLA expression, or 'null' if no result has been
        // computed yet.
        this.val = val;

        // @type: TLAState
        // Represents the current assignment of values to variables in an
        // in-progress expression evaluation. Right now simply a mapping from
        // variable names to TLA values.
        this.state = state;

        // @type: Object
        // Global definitions that exist in the specification, stored as mapping
        // from definition names to their syntax tree node.
        this.defns = defns;

        // @type: string -> TLCValue
        // Currently bound identifiers in the in-progress expression evaluation,
        // stored as a mapping from identifier names to their TLC values.
        this.quant_bound = quant_bound;
    }

    /**
     * Returns a new copy of this context with 'val' updated to the given value.
     * @param {TLCValue} valNew 
     */
    withVal(valNew){
        let ctxCopy = _.cloneDeep(this);
        ctxCopy["val"] = valNew;
        return ctxCopy;
    }

    /**
     * Returns a new copy of this context with 'state' updated to the given value.
     * @param {Object} stateNew 
     */
    withState(stateNew){
        let ctxCopy = _.cloneDeep(this);
        ctxCopy["state"] = stateNew;
        return ctxCopy;
    }
}


function evalLand(lhs, rhs, ctx){
    assert(ctx instanceof Context);

    // Evaluate left to right.
    evalLog("## LAND - LHS:", lhs.text, ", RHS: ", rhs.text);
    let lhsEval = _.flattenDeep(evalExpr(lhs, ctx));
    evalLog("lhsEval:", lhsEval);
    let rhsEval = lhsEval.map(lctx => {
        evalLog("rhs:", rhs.text);
        evalLog("lctx:", lctx);
        return evalExpr(rhs, lctx).map(actx => {
            return [actx.withVal((lctx["val"] && actx["val"])).withState(actx["state"])];
        })
    });
    return _.flattenDeep(rhsEval);
}

function evalLor(lhs, rhs, ctx){
    assert(ctx instanceof Context);

    // return {"val": false, "states": vars};
    evalLog("## LOR");
    evalLog("orig ctx:", ctx);
    // For all existing possible variable assignments split into
    // separate evaluation cases for left and right branch.
    let ctxLhs = evalExpr(lhs, ctx);
    evalLog("lhs ctx:",ctxLhs);
    let ctxRhs = evalExpr(rhs, ctx);
    return ctxLhs.concat(ctxRhs);
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

function evalEq(lhs, rhs, ctx){
    assert(ctx instanceof Context);

    // Deal with equality of variable on left hand side.
    let identName = lhs.text;

    // let isUnprimedVar = ctx[0]["state"].hasOwnProperty(varName) && !isPrimedVar(lhs);
    let isUnprimedVar = ctx["state"].hasOwnProperty(identName) && !isPrimedVar(lhs);
    // console.log("isUnprimedVar:", isUnprimedVar);

    if(isPrimedVar(lhs) || (isUnprimedVar && !ASSIGN_PRIMED)){
        // Update assignments for all current evaluation ctx.

        // If, in the current state assignment, the variable has not already
        // been assigned a value, then assign it.If it has already been assigned,
        // then check for equality.
        // Variable already assigned in this context. So, check for equality.
        if(ctx["state"].hasOwnProperty(identName) && ctx["state"][identName] !== null){
            evalLog("Variable '" + identName + "' already assigned in ctx:",  ctx);
            let rhsVals = evalExpr(rhs, ctx);
            console.assert(rhsVals.length === 1);
            let rhsVal = rhsVals[0]["val"]
            evalLog("rhsVal:", rhsVal);
            let boolVal = (ctx["state"][identName] === rhsVal)
            evalLog("boolVal:", boolVal);

            return [ctx.withVal(boolVal)];
        }

        // Variable not already assigned. So, update variable assignment as necessary.
        let stateUpdated = _.mapValues(ctx["state"], (val,key,obj) => {
            if(key === identName){
                evalLog("Variable (" + identName + ") not already assigned in ctx:",  ctx);
                let rhsVals = evalExpr(rhs, _.cloneDeep(ctx));
                console.assert(rhsVals.length === 1);
                let rhsVal = rhsVals[0]["val"];
                evalLog("Variable (" + identName + ") getting value:",  rhsVal);
                return (val === null) ? rhsVal : val;
            } 
            return val;
        });
        evalLog("state updated:", stateUpdated);
        return [ctx.withVal(true).withState(stateUpdated)];

    } else{
        evalLog(`Checking for equality of ident '${identName}' with '${rhs.text}'.`, ctx);
        
        // Evaluate left and right hand side.
        let lhsVals = evalExpr(lhs, _.cloneDeep(ctx));
        console.assert(lhsVals.length === 1);
        let lhsVal = lhsVals[0]["val"];
        // console.log("Checking for, lhsVal", lhsVal);

        let rhsVals = evalExpr(rhs, _.cloneDeep(ctx));
        console.assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        // console.log("Checking for, rhsVal", rhsVal);

        // Check equality.
        const boolVal = _.isEqual(lhsVal, rhsVal);
        // console.log("Checking for, boolVal:", boolVal);

        // Return context with updated value.
        return [ctx.withVal(boolVal)];
    }
}

// 'vars' is a list of possible partial state assignments known up to this point.
function evalBoundInfix(node, ctx){
    assert(ctx instanceof Context);

    evalLog("evalBoundInfix:", node);

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
        let mulLhsVal = evalExpr(lhs, ctx);
        evalLog("mul lhs val:", mulLhsVal);
        let lhsVal = mulLhsVal[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outVal = lhsVal * rhsVal;
        // console.log("mul overall val:", outVal);
        return [ctx.withVal(outVal)];
    }

    // Plus.
    if(symbol.type === "plus"){
        evalLog("plus lhs:", lhs, lhs.text);
        let plusLhsVal = evalExpr(lhs, ctx);
        evalLog("plus lhs val:", plusLhsVal);
        let lhsVal = plusLhsVal[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outVal = lhsVal + rhsVal;
        return [ctx.withVal(outVal)];
    }

    // Greater than.
    if(symbol.type === "gt"){
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outVal = lhsVal > rhsVal;
        return [ctx.withVal(outVal)];
    }

    if(symbol.type === "geq"){
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        let outVal = lhsVal >= rhsVal;
        return [ctx.withVal(outVal)];
    }

    // Disjunction.
    if(symbol.type === "lor"){
        return evalLor(lhs, rhs, ctx);
    }

    if(symbol.type === "land"){
        return evalLand(lhs, rhs, ctx);
    }

    // Equality.
    if(symbol.type ==="eq"){
        // console.log("bound_infix_op, symbol 'eq', ctx:", JSON.stringify(ctx));
        evalLog("bound_infix_op -> (eq), ctx:", ctx);
        return evalEq(lhs, rhs, ctx);
    } 

    // Inequality.
    if(symbol.type ==="neq"){
        // console.log("bound_infix_op, symbol 'neq', ctx:", JSON.stringify(ctx));
        evalLog("bound_infix_op -> (neq), ctx:", ctx);
        
        let lident = lhs.text;
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        // console.log("Checking for inequality with var:", varName);
        let rhsVals = evalExpr(rhs, ctx);
        console.assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        let boolVal = !_.isEqual(lhsVal, rhsVal);
        // console.log("inequality lhsVal:", lhsVal);
        // console.log("inequality rhsVal:", rhsVal);
        evalLog("inequality boolVal:", boolVal);
        // Return context with updated value.
        return [ctx.withVal(boolVal)];
    } 

    // Set membership.
    if(symbol.type ==="in"){
        // console.log("bound_infix_op, symbol 'in', ctx:", ctx);
        evalLog("bound_infix_op, symbol 'in', ctx:", ctx);
        let lhs = node.namedChildren[0];
        let rhs = node.namedChildren[2];

        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("setin lhsval:", lhsVal, lhs.text, ctx);

        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("setin rhsval:", rhsVal, rhs.text, ctx);

        evalLog("setin lhs in rhs:", rhsVal.includes(lhsVal));
        return [ctx.withVal(rhsVal.includes(lhsVal))];
    } 
    
    // Set intersection.
    if(symbol.type ==="cap"){
        evalLog("bound_infix_op, symbol 'cap'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("cap lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("cap rhs:", rhsVal);
        let capVal = _.intersectionWith(lhsVal, rhsVal, _.isEqual);
        return [ctx.withVal(capVal)];
    } 

    // Set union.
    if(symbol.type ==="cup"){
        // console.log("bound_infix_op, symbol 'cup'");
        evalLog("bound_infix_op, symbol 'cup'");
        // TODO: Will eventually need to figure out a more principled approach to object equality.
        evalLog(lhs);
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        evalLog("cup lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        evalLog("cup rhs:", lhsVal);
        return [ctx.withVal(_.uniq(lhsVal.concat(rhsVal)))];
    }   

    // Set minus.
    if(symbol.type ==="setminus"){
        // console.log("bound_infix_op, symbol 'setminus'");
        evalLog("bound_infix_op, symbol 'setminus'");
        // TODO: Will need to figure out a more principled approach to object equality.
        console.log(lhs);
        let lhsVal = evalExpr(lhs, ctx)[0]["val"];
        console.log("setminus lhs:", lhsVal);
        let rhsVal = evalExpr(rhs, ctx)[0]["val"];
        console.log("setminus rhs:", lhsVal);
        return [ctx.withVal(_.difference(lhsVal,rhsVal))];
    }  
}

function evalDisjList(parent, disjs, ctx){
    assert(ctx instanceof Context);

    evalLog("eval: disjunction list!");

    // Split into separate evaluation cases for each disjunct.
    return _.flattenDeep(disjs.map(disj => evalExpr(disj, ctx)));

    // let newContexts = disjs.map(disj => evalExpr(disj, contexts));
    // console.log("newContexts:", newContexts);
    // return _.flatten(newContexts);

    // let contextsLhs = evalExpr(lhs, contexts);
    // let contextsRhs = evalExpr(rhs, contexts);
    // return contextsLhs.concat(contextsRhs);
}

function evalConjList(parent, conjs, ctx){
    assert(ctx instanceof Context);

    evalLog("evalConjList -> ctx:", ctx);

    // Initialize boolean value if needed.
    if(ctx["val"]===null){
        ctx["val"]=true;
    }
    return conjs.reduce((prev,conj) => {
        let res = prev.map(ctxPrev => {
            // If this context has already evaluated to false, then the overall
            // conjunction list will evaluate to false, so we can short-circuit
            // the expression evaluation and terminate early.
            if(ctxPrev["val"]===false){
                return ctxPrev;
            }

            return evalExpr(conj, ctxPrev).map(ctxCurr => ctxCurr.withVal(ctxCurr["val"] && ctxPrev["val"]));
        });
        evalLog("evalConjList mapped: ", res);
        return _.flattenDeep(res);
    }, [ctx]);
}

function evalIdentifierRef(node, ctx){
    assert(ctx instanceof Context);

    let ident_name = node.text;
    evalLog(`evalIdentifierRef, '${node.text}' context:`, ctx);

    // If this identifier refers to a variable, return the value bound
    // to that variable in the current context.
    if(ctx["state"].hasOwnProperty(ident_name)){
        evalLog("variable identifier: ", ident_name);
        let var_val = ctx["state"][ident_name];
        evalLog("var ident context:", ctx["state"], var_val);
        return [ctx.withVal(var_val)];
    }

    // See if the identifier is bound to a value in the current context.
    // If so, return the value it is bound to.
    if(ctx.hasOwnProperty("quant_bound") && ctx["quant_bound"].hasOwnProperty(ident_name)){
        let bound_val = ctx["quant_bound"][ident_name];
        evalLog("bound_val", bound_val);
        return [ctx.withVal(bound_val)];
    }

    // See if this identifier is a definition in the spec.
    if(ctx["defns"].hasOwnProperty(ident_name)){
        // Evaluate the definition in the current context.
        // TODO: Consider defs that are n-ary operators.
        let defNode = ctx["defns"][ident_name]["node"];
        return evalExpr(defNode, ctx);
    }

    // TODO: Consider case of being undefined.
}

// \E x,...,xn \in <D1>, y1,...,yn \in <D2> : <expr>
// \A x,...,xn \in <D1>, y1,...,yn \in <D2> : <expr>
function evalBoundedQuantification(node, ctx){
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
        expr = evalExpr(qbound.children[2], ctx);
        let domain = expr[0]["val"];
        return domain;
    });
    let quantIdents = quantBounds.map(qbound => qbound.children[0].text);

    // Iterate over the product of all quantified domains and evaluate
    // the quantified expression with the appropriately bound values.
    let quantDomainTuples = cartesianProductOf(...quantDomains);
    evalLog("quantDomain tuples:", quantDomainTuples);
    if(quantDomainTuples.length === 0){
        return [ctx.withVal(false)];
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
        let ret = evalExpr(quant_expr, _.cloneDeep(boundContext));
        return ret;
    }));    
}

// <op>(<arg1>,...,<argn>)
function evalBoundOp(node, ctx){
    assert(node.type === "bound_op");

    let opName = node.namedChildren[0].text;
    evalLog("bound_op:", opName);
    evalLog("bound_op context:",ctx);

    // Built in operator.
    if(opName == "Cardinality"){
        let argExpr = node.namedChildren[1];
        let argExprVal = evalExpr(argExpr, ctx)[0]["val"]
        evalLog("Cardinality val:", argExpr.text, argExprVal.length);
        return [ctx.withVal(argExprVal.length)];
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
        if(opArgs.length >= 1){
            // Evaluate each operator argument.
            let opArgsEvald = node.namedChildren.slice(1).map(oarg => evalExpr(oarg, ctx));
            let opArgVals = _.flatten(opArgsEvald);
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
            return evalExpr(opDefNode, opEvalContext);
        }
    }
}

/**
 * Evaluate a TLC expression for generating initial/next states.
 * 
 * In the simplest case, expression evaluation simply takes in an expression and
 * returns a TLA value. When we are evaluating an expression in the form of an
 * initial state or next state predicate, however, things are more involved. 
 * 
 * That is, when evaluating an initial/next state predicate for generating
 * states, evaluation returns both a boolean value (TRUE/FALSE) as well as an
 * assignment of values to variables. For example, in the context of initial
 * state generation, this is an assignment of values to all variables x1,...,xn
 * declared in a specification. In the context of next state generation, this is
 * an assignment of values to all variables x1,...,xn,x1',...,xn' i.e. the
 * "current" state variables and the "next"/"primed" copy of the state
 * variables. 
 * 
 * Additionally, when generating states during this type of evaluation, we may
 * produce not only a single return value, but a set of return values. That is,
 * we may have one return value for each potential "branch" of the evaluation,
 * corresponding to possible disjunctions that appear in a predicate. For
 * example, the initial state predicate x = 0 \/ x = 1 will produce two possible
 * return values, both of which evaluate to TRUE and which assign the values of
 * 0 and 1, respectively, to the variable 'x'.
 * 
 * To handle this type of evaluation strategy, we allow expression evaluation to
 * take in a current 'Context' object, which consists of several items for
 * tracking data needed during evaluation. See the fields of the 'Context' class
 * definition for an explanation of what data is tracked during expression
 * evaluation.
 * 
 * Expression evaluation can return a list of these context objects, one for
 * each potential evaluation branch of a given expression. Each returned context
 * can contain an assignment of values to variables along with a return value
 * for that expression.
 *
 * In our implementation, we have each evaluation handler function (i.e.
 * 'eval<NAME>') take in a single context object, and return potentially many
 * contexts. This makes it easier to implement each evaluation handler function,
 * by focusing just on how to evaluate an expression given a single context, and
 * either update it, or fork it into multiple new sub-contexts. From this
 * perspective, we can think about the overall evaluation computation as a tree,
 * where each evaluation function takes in a single branch of the tree, and may
 * potentially create several new forks in the tree, corresponding to separate
 * evaluation sub-branches. When the overall computation terminates, each leaf
 * of the tree should represent the result of one evaluation branch, which will
 * contain both a return value for the expression and a potential assignment of
 * values to variables.
 * 
 * @param {TLASyntaxNode} node: TLA+ tree sitter syntax node representing the expression to evaluate.
 * @param {Context} ctx: a 'Context' instance under which to evaluate the given expression.
 * @returns 
 */
function evalExpr(node, ctx){
    // TODO: Enable this after argument conversion.
    assert(ctx instanceof Context);

    // console.log("$$ evalExpr, node: ", node, node.text);
    evalLog("evalExpr -> ("+ node.type + ") '" + node.text + "'");

    // [<lExpr> EXCEPT ![<updateExpr>] = <rExpr>]
    if(node.type === "except"){
        evalLog("EXCEPT node, ctx:", ctx);
        let lExpr = node.namedChildren[0];
        let updateExpr = node.namedChildren[1];
        let rExpr = node.namedChildren[2];

        // This value should be a function.
        evalLog("lExpr:",lExpr); 
        let lExprVal = evalExpr(lExpr, ctx);
        evalLog("lexprval:", lExprVal);
        // console.assert(lExprVal.type === "function");
        let fnVal = lExprVal[0]["val"];
        evalLog("fnVal:",fnVal);

        evalLog(updateExpr);
        let updateExprVal = evalExpr(updateExpr, ctx)[0]["val"];
        evalLog("updateExprVal:", updateExprVal);

        let rExprVal = evalExpr(rExpr, ctx)[0]["val"];
        evalLog("rExprVal:", rExprVal);
        fnVal[updateExprVal] = rExprVal;

        return [ctx.withVal(_.cloneDeep(fnVal))];

        throw Error("Evaluation of 'except' node type not implemented.");

    }

    // <fnVal>[<fnArgVal>] e.g. 'f[3]'
    if(node.type === "function_evaluation"){
        evalLog("function_evaluation: ", node.text);

        let fnVal = evalExpr(node.namedChildren[0], ctx)[0]["val"];
        // console.log("fnArg node: ", node.namedChildren[1]);
        // let fnArgVal = evalExpr(node.namedChildren[1], ctx);
        // console.log("fnArgVal:", fnArgVal);
        let fnArgVal = evalExpr(node.namedChildren[1], ctx)[0]["val"];
        evalLog("fneval (arg,val): ", fnVal, ",", fnArgVal);
        return [ctx.withVal(fnVal[fnArgVal])];
    }


    if(node.type === "comment"){
        // TOOD: Handle properly.
    }
    if(node === undefined){
        return [ctx.withVal(false)];
    }
    if(node.type === "conj_list"){
        let ret =  evalConjList(node, node.children, ctx);
        evalLog("evalConjList ret: ", ret);
        return ret;
    }  
    if(node.type === "disj_list"){
        return evalDisjList(node, node.children, ctx);
    }  
    if(node.type === "conj_item"){
        conj_item_node = node.children[1];
        return evalExpr(conj_item_node, ctx);
    }
    if(node.type === "disj_item"){
        disj_item_node = node.children[1];
        return evalExpr(disj_item_node, ctx);
    }

    if(node.type === "bound_op"){
        return evalBoundOp(node, ctx)
    }

    if(node.type === "bound_infix_op"){
        // evalLog(node.type + ", ", node.text, ", ctx:", JSON.stringify(contexts));
        return evalBoundInfix(node, ctx);
    }

    if(node.type === "bound_prefix_op"){
        let symbol = node.children[0];
        let rhs = node.children[1];
        evalLog(node.type, ", ", node.text, `, prefix symbol: '${symbol.type}' `, "ctx:", ctx);
        if(symbol.type === "powerset"){
            evalLog("POWERSET op");
            evalLog(rhs);
            let rhsVal = evalExpr(rhs, ctx);
            evalLog("rhsVal: ", rhsVal);
            rhsVal = rhsVal[0]["val"];
            let powersetRhs = subsets(rhsVal);
            evalLog("powerset:",powersetRhs);
            return [ctx.withVal(powersetRhs)];
        }
        if(symbol.type === "negative"){
            let rhsVal = evalExpr(rhs, ctx);
            rhsVal = rhsVal[0]["val"];
            return [ctx.withVal(-rhsVal)];
        }   

        if(symbol.type === "lnot"){
            let rhsVal = evalExpr(rhs, ctx);
            rhsVal = rhsVal[0]["val"];
            return [ctx.withVal(!rhsVal)];
        }   
    }

    // TODO: Finish this after implementing 'except' node type handling.
    if(node.type === "bounded_quantification"){
        return evalBoundedQuantification(node, ctx);
    }

    if(node.type === "identifier_ref"){
        return evalIdentifierRef(node, ctx);
    }

    if(node.type === "nat_number"){
        // console.log(node.type, node.text);
        return [ctx.withVal(parseInt(node.text))];
    }

    if(node.type === "boolean"){
        evalLog(node.type, node.text);
        let boolVal = node.text === "TRUE" ? true : false;
        return [ctx.withVal(boolVal)];
    }

    if(node.type === "string"){
        evalLog("string node", node.text);
        // Remove the quotes.
        let rawStr = node.text.substring(1,node.text.length-1);
        return [ctx.withVal(rawStr)];
    }

    if(node.type === "if_then_else"){
        let cond = node.namedChildren[0];
        let thenNode = node.namedChildren[1];
        let elseNode = node.namedChildren[2];

        let condVal = evalExpr(cond, _.cloneDeep(ctx))[0]["val"];
        if(condVal){
            let thenVal = evalExpr(thenNode, _.cloneDeep(ctx));
            evalLog("thenVal", thenVal, thenNode.text);
            return thenVal;
        } else{
            let elseVal = evalExpr(elseNode, _.cloneDeep(ctx));
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
        let domainExprVal = evalExpr(domainExpr, ctx)[0]["val"];
        
        evalLog("domainExprVal:", domainExprVal);

        // Return all values in domain for which the set filter evaluates to true.
        let filteredVals = domainExprVal.filter(exprVal => {
            // Evaluate rhs in context of the bound value and check its truth value.
            let boundContext = _.cloneDeep(ctx);
            if(!boundContext.hasOwnProperty("quant_bound")){
                boundContext["quant_bound"] = {};
            }
            boundContext["quant_bound"][ident] = exprVal;
            evalLog("rhsFilterVal:", evalExpr(rhsFilter, boundContext));
            let rhsFilterVal = evalExpr(rhsFilter, boundContext)[0]["val"];
            return rhsFilterVal;
        });
        evalLog("domainExprVal filtered:", filteredVals);
        return [ctx.withVal(filteredVals)];
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
            let r = evalExpr(child, ctx);
            console.assert(r.length === 1);
            return r[0]["val"];
        });
        ret = _.flatten(ret);
        // console.log(ret);
        return [ctx.withVal(ret)];

        // let ret = node.children.map(child => evalExpr(child, ctx));
        // console.log(_.flatten(ret));
        return ret;
    }

    // <record>.<field>
    if(node.type === "record_value"){
        evalLog("RECVAL", node);
        let rec = node.namedChildren[0];
        let recField = node.namedChildren[1].text;

        let recVal = evalExpr(rec, ctx)[0]["val"];
        evalLog("recVal", recVal);
        evalLog("recField", recField);
        let fieldVal = recVal[recField];
        return [ctx.withVal(fieldVal)];

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
            let exprVal = evalExpr(exprNode, ctx);
            record_obj[identName] = exprVal[0]["val"];
        }
        evalLog("RECOBJ", record_obj);
        return [ctx.withVal(record_obj)];
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
        quant_expr = evalExpr(quant_bound.children[2], ctx);
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
            let vals = evalExpr(fexpr, boundContext);
            evalLog("fexpr vals:", vals);
            console.assert(vals.length === 1);
            fnVal[v] = vals[0]["val"];
        }
        evalLog("fnVal:", fnVal);
        return [ctx.withVal(fnVal)];
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
    let ret_ctxs = evalExpr(initDef, initCtx);
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

    let initCtx = new Context(null, currStateVars, defns, {});
    console.log("currStateVars:", currStateVars);
    let ret = evalExpr(nextDef, initCtx);
    // console.log("getNextStates ret:", ret);

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
    initStates = initStates.filter(actx => actx["val"]).map(actx => actx["state"]);
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
    initStates = initStates.filter(actx => actx["val"]).map(actx => actx["state"]);

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

let origevalExpr = evalExpr;
evalExpr = function(...args){
    depth += 1;
    let ret = origevalExpr(...args);
    evalLog("evalreturn -> ", ret, args[0].text);
    depth -= 1;
    return ret;
}

let origevalBoundInfix = evalBoundInfix;
evalBoundInfix = function(...args){
    depth += 1;
    let ret = origevalBoundInfix(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}

let origevalConjList = evalConjList;
evalConjList = function(...args){
    depth += 1;
    let ret = origevalConjList(...args);
    evalLog("evalreturn -> ", ret);
    depth -= 1;
    return ret;
}
