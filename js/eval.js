//
// TLA+ interpreter. 
//
// Contains logic for expression evaluation and initial/next generation.
//


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
            cursor.gotoFirstChild();

            // The definition identifier name.
            node = cursor.currentNode()
            // console.log(node.text)
            console.assert(node.type === "identifier");
            let opName = node.text;
            
            // def_eq (skip)
            cursor.gotoNextSibling();
            // console.log(cursor.currentNode().text)

            // The definition node.
            cursor.gotoNextSibling();
            // console.log(cursor.currentNode().text)
            let def = cursor.currentNode();

            // console.log(cursor.currentNode());
            // let var_ident = cursor.currentNode();
            cursor.gotoParent();
            // Save the variable declaration.
            // var_decls[var_ident.text] = {"id": node.id}; 
            op_defs[opName] = def;
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
    console.log("###### LAND");
    let lhsEval = _.flattenDeep(evalInitExpr(lhs, contexts));
    console.log("lhsEval:", lhsEval);
    let rhsEval = lhsEval.map(lctx => {
        return evalInitExpr(rhs, lctx).map(rctx => {
            return ({"val": (lctx["val"] && rctx["val"]), "state": rctx["state"]})
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
    console.log("###### LOR");
    console.log("orig ctx:", JSON.stringify(contexts));
    // For all existing possible variable assignments split into
    // separate evaluation cases for left and right branch.
    let contextsLhs = evalInitExpr(lhs, contexts);
    console.log("lhs contexts:",contextsLhs);
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
    let varName = lhs.text;

    // let isUnprimedVar = contexts[0]["state"].hasOwnProperty(varName) && !isPrimedVar(lhs);
    let isUnprimedVar = contexts["state"].hasOwnProperty(varName) && !isPrimedVar(lhs);
    console.log("isUnprimedVar:", isUnprimedVar);

    if(isPrimedVar(lhs) || (isUnprimedVar && !ASSIGN_PRIMED)){
        // Update assignments for all current evaluation contexts.

        // If, in the current state assignment, the variable has not already
        // been assigned a value, then assign it.If it has already been assigned,
        // then check for equality.
        // Variable already assigned in this context. So, check for equality.
        if(contexts["state"].hasOwnProperty(varName) && contexts["state"][varName] !== null){
            console.log("Variable '" + varName + "' already assigned in ctx:",  contexts);
            let rhsVals = evalInitExpr(rhs, contexts);
            console.assert(rhsVals.length === 1);
            let rhsVal = rhsVals[0]["val"]
            console.log("rhsVal:", rhsVal);
            let boolVal = (contexts["state"][varName] === rhsVal)
            console.log("boolVal:", boolVal);
            return [{"val": boolVal, "state": contexts["state"]}]; 
        }

        // Variable not already assigned. So, update variable assignment as necessary.
        let stateUpdated = _.mapValues(contexts["state"], (val,key,obj) => {
            console.log("Variable '" + varName + "' not already assigned in ctx:",  contexts);
            if(key === varName){
                let rhsVals = evalInitExpr(rhs, contexts);
                console.assert(rhsVals.length === 1);
                let rhsVal = rhsVals[0]["val"];
                return (val === null) ? rhsVal : val;
            } 
            return val;
        })
        return [{"val": true, "state": stateUpdated}];
    } else{
        let varName = lhs.text;
        console.log("Checking for equality with var:", varName);
        // Check equality of variable with expression.
        // TODO: Check for variable name properly.
        let rhsVals = evalInitExpr(rhs, contexts);
        console.assert(rhsVals.length === 1);
        let rhsVal = rhsVals[0]["val"];
        let boolVal = (contexts["state"][varName] === rhsVal);
        console.log("boolVal:", boolVal);
        return [{"val": boolVal, "state": contexts["state"]}]; 
    }

}

// 'vars' is a list of possible partial state assignments known up to this point.
function evalInitBoundInfix(node, contexts){
    // lhs.
    let lhs = node.children[0];
    // symbol.
    let symbol = node.children[1];
    // console.log("symbol:", node.children[1]);
    // rhs
    let rhs = node.children[2];

    // Disjunction.
    if(symbol.type === "lor"){
        return evalInitLor(lhs, rhs, contexts);
    }

    if(symbol.type === "land"){
        return evalInitLand(lhs, rhs, contexts);
    }

    // Equality.
    if(symbol.type ==="eq"){
        console.log("bound_infix_op, symbol 'eq'");
        return evalInitEq(lhs, rhs, contexts);
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
    console.log("evalInit: conjunction list!");
    console.log("evalInit: node children:", parent.children);
    console.log(parent.text);

    return conjs.reduce((prevRes,currConj) => {
        return _.flattenDeep(prevRes.map(ctx => evalInitExpr(currConj, ctx)))
    }, [contexts]);

    // let currContexts = _.cloneDeep(contexts);
    // for(const child of conjs){
    //     console.log("currContexts:", currContexts);
    //     currContexts = evalInitExpr(child, currContexts);
    // }
    // console.log("newContexts:", currContexts);
    // return currContexts;    
}

// Evaluation of a TLC expression in the context of initial state generation
// can produce a few outcomes. Either, it simply updates the current assignment
// of values to variables, and/or it creates a new branch in the state computation,
// arising from presence of a disjunction (i.e. existential quantifier/set membership, etc.)

// 
// Evaluation of an individual expression always takes place under some
// 'context' i.e. a current assignment of values to variables. Evaluation of a
// sub expression can either:
// 
//  - Update the current context i.e. the current variable assignment
//  - Return an atomic value.
//  - Fork the current evaluation context into multiple, new contexts (e.g. via disjunction)
// 
// The return value of an expression evaluation is not always a single object. It can be a set
// of return objects, if the evaluation computation forked into multiple contexts. Each context
// is a separate computation, so it has its own expression value that it will return, along with
// any generated states i.e. the assignments to variables that were produced on that 
// evaluation branch.
// 
//
// So, evaluation of a single expression should return a list of (value, state)
// pairs. Each individual evaluation helper function, however, can take in a
// single expression and context, as opposed to a list of contexts.
//

function evalInitExpr(node, contexts){
    if(node === undefined){
        return [{"val": false, "state": {}}];
    }
    if(node.type === "conj_list"){
        return evalInitConjList(node, node.children, contexts);
    }  
    if(node.type === "disj_list"){
        return evalInitDisjList(node, node.children, contexts);
    }  
    if(node.type === "conj_item"){
        conj_item_node = node.children[1];
        return evalInitExpr(conj_item_node, contexts);
    }
    if(node.type === "disj_item"){
        disj_item_node = node.children[1];
        return evalInitExpr(disj_item_node, contexts);
    }
    if(node.type === "bound_infix_op"){
        console.log(node.type, "| ", node.text);
        return evalInitBoundInfix(node, contexts);
    }

    if(node.type === "identifier_ref"){
        //TODO.
        console.log("identifier_ref");
        console.log(node.type);
        console.log(node.text);
    }
    if(node.type === "nat_number"){
        console.log(node.type, node.text);
        return [{"val": parseInt(node.text), "state": {}}];
    }

    // TODO: Re-examine whether this implementation is correct.
    if(node.type ==="finite_set_literal"){
        console.log(node.children);

        // TODO: Check the computation below for correctness.

        // Remove the outer braces, "{" and "}"
        let innerChildren = node.children.slice(1,node.children.length-1);
        // Remove commas and then evaluate each set element.
        let ret = innerChildren.filter(child => child.type !== ",")
        ret = ret.map(child => {
            // TODO: For now assume set elements don't fork evaluation context.
            let r = evalInitExpr(child, contexts);
            console.assert(r.length === 1);
            return r[0]["val"];
        });
        ret = _.flatten(ret);
        console.log(ret);
        return [{"val": ret, "state": contexts["state"]}];

        // let ret = node.children.map(child => evalInitExpr(child, contexts));
        // console.log(_.flatten(ret));
        return ret;
    }

    // "[" <quantifier_bound> "|->" <expr> "]"
    if(node.type === "function_literal"){
        console.log(node.children);
        // lbracket = node.children[0]
        // rbracket = node.children[4];
        let quant_bound = node.children[1];
        let all_map_to = node.children[2];
        console.assert(all_map_to.type === "all_map_to");
        let fexpr = node.children[3];

        // Handle the quantifier bound:
        // <identifier> \in <expr>
        quant_ident = quant_bound.children[0];
        quant_expr = evalInitExpr(quant_bound.children[2], contexts);
        console.log("quant_expr:", quant_expr);
        console.log(quant_ident.type);
        console.log(quant_expr.type);

        // Evaluate the quantified expression for each element in the 
        // quantifier domain.
        // TODO: Implement this.

    }
}

/**
 * Generates all possible initial states given the syntax tree node for the
 * initial state predicate and an object 'vars' which contains exactly the
 * specification's state variables as keys.
 */
function getInitStates(initDef, vars){
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
    let init_ctx = {"val": null, "state": init_var_vals};
    // let ret_ctxs = evalInitExpr(initDef, [init_ctx]);
    let ret_ctxs = evalInitExpr(initDef, init_ctx);
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
function getNextStates(nextDef, currStateVars){
    // TODO: Pass this variable value as an argument to the evaluation functions.
    ASSIGN_PRIMED = true;

    for(var k in currStateVars){
        let primedVar = k + "'";
        currStateVars[primedVar] = null;
    }
    console.log("currStateVars:", currStateVars);
    // let init_ctxs = [{"val": null, "state": currStateVars}]
    let init_ctx = {"val": null, "state": currStateVars};
    // let ret = evalNextExpr(nextDef, init_ctxs);
    let ret = evalInitExpr(nextDef, init_ctx);
    console.log("getNextStates ret:", ret);
    // Only include evaluations that were TRUE.
    return ret;
    // return ret.filter(c => c["val"]);
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

    let initStates = getInitStates(initDef, vars);
    // Keep only the valid states.
    initStates = initStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);
    console.log("initial states:", initStates);

    console.log("INITIAL STATES:");
    for(const state of initStates){
        console.log(state);
    }

    let nextDef = defns["Next"];
    console.log("<<<< NEXT >>>>");
    console.log(nextDef);
    console.log("nextDef.childCount: ", nextDef.childCount);
    console.log("nextDef.type: ", nextDef.type);

    // // let currState = initStates[0]["state"];
    let allNext = []
    for(const istate of initStates){
        let currState = _.cloneDeep(istate);
        console.log("$$$ Computing next states from current state: ", currState);
        let ret = getNextStates(nextDef, currState);
        console.log(ret);
        allNext = allNext.concat(ret);
    }

    console.log("NEXT STATES:");
    for(const ctx of allNext){
        console.log(ctx["val"], ctx["state"]);
    }
    return {"initStates": initStates, "nextStates": allNext};
}