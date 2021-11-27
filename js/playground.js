let tree;

(async () => {
  const CAPTURE_REGEX = /@\s*([\w\._-]+)/g;
  const COLORS_BY_INDEX = [
    'blue',
    'chocolate',
    'darkblue',
    'darkcyan',
    'darkgreen',
    'darkred',
    'darkslategray',
    'dimgray',
    'green',
    'indigo',
    'navy',
    'red',
    'sienna',
  ];

  console.log("WILL")

  const scriptURL = document.currentScript.getAttribute('src');

  const codeInput = document.getElementById('code-input');
  const languageSelect = document.getElementById('language-select');
  const loggingCheckbox = document.getElementById('logging-checkbox');
  const outputContainer = document.getElementById('output-container');
  const outputContainerScroll = document.getElementById('output-container-scroll');
  const playgroundContainer = document.getElementById('playground-container');
  const queryCheckbox = document.getElementById('query-checkbox');
  const queryContainer = document.getElementById('query-container');
  const queryInput = document.getElementById('query-input');
  const updateTimeSpan = document.getElementById('update-time');
  const languagesByName = {};

  loadState();

  await TreeSitter.init();

  const parser = new TreeSitter();

  let tree = null;

//   const codeEditor = CodeMirror.fromTextArea(codeInput, {
//     lineNumbers: true,
//     showCursorWhenSelecting: true
//   });

//   const queryEditor = CodeMirror.fromTextArea(queryInput, {
//     lineNumbers: true,
//     showCursorWhenSelecting: true
//   });

//   const cluster = new Clusterize({
//     rows: [],
//     noDataText: null,
//     contentElem: outputContainer,
//     scrollElem: outputContainerScroll
//   });
//   const renderTreeOnCodeChange = debounce(renderTree, 50);
//   const saveStateOnChange = debounce(saveState, 2000);
//   const runTreeQueryOnChange = debounce(runTreeQuery, 50);

  let languageName = languageSelect.value;
  let treeRows = null;
  let treeRowHighlightedIndex = -1;
  let parseCount = 0;
  let isRendering = 0;
  let query;

//   codeEditor.on('changes', handleCodeChange);
//   codeEditor.on('viewportChange', runTreeQueryOnChange);
//   codeEditor.on('cursorActivity', debounce(handleCursorMovement, 150));
//   queryEditor.on('changes', debounce(handleQueryChange, 150));

//   loggingCheckbox.addEventListener('change', handleLoggingChange);
//   queryCheckbox.addEventListener('change', handleQueryEnableChange);
//   languageSelect.addEventListener('change', handleLanguageChange);
//   outputContainer.addEventListener('click', handleTreeClick);

//   handleQueryEnableChange();
  await handleLanguageChange()

//   playgroundContainer.style.visibility = 'visible';

function walkTree(tree, specLines){

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
        console.log(node);
        console.log("node type:");
        console.log(node.type);
        console.log("node text:");
        console.log(node.text);
        console.log("node id:");
        console.log(node.id);

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
            console.log(node.text)
            console.assert(node.type === "identifier");
            let opName = node.text;
            
            // def_eq (skip)
            cursor.gotoNextSibling();
            console.log(cursor.currentNode().text)

            // The definition node.
            cursor.gotoNextSibling();
            console.log(cursor.currentNode().text)
            let def = cursor.currentNode();

            // console.log(cursor.currentNode());
            // let var_ident = cursor.currentNode();
            cursor.gotoParent();
            // Save the variable declaration.
            // var_decls[var_ident.text] = {"id": node.id}; 
            op_defs[opName] = def;
        }
        console.log("++++")
    }

    console.log(var_decls);
    console.log(op_defs);

    objs = {
        "var_decls": var_decls,
        "op_defs": op_defs
    }

    // console.log(cursor.currentNode().toString());
    return objs;

    // s1 = cursor.gotoNextSibling();
    // console.log(s1);
    // console.log(cursor.nodeType);
    // s1 = cursor.gotoFirstChild();
    // console.log(s1);
    // console.log(cursor.nodeType);

    // Go down to the top-level module.
    s1 = cursor.gotoFirstChild();
    console.log(cursor.nodeType);

    console.log("++++++++++")
    // s1 = cursor.gotoNextSibling();
    // console.log(cursor.nodeType);

    start = cursor.startPosition;
    end = cursor.endPosition;
    id = cursor.nodeId;
    // console.log(start, end)

    // Go to the first child of the MODULE.
    s1 = cursor.gotoFirstChild();
    console.log(cursor.nodeType);

    function get_ident_name(cursor){
        start = cursor.startPosition;
        end = cursor.endPosition;
        id = cursor.nodeId;
        ident_str = specLines[start["row"]].substring(start["column"], end["column"]);
        return ident_str;
        // lines[start.row]
    }

    // start = cursor.startPosition;
    // end = cursor.endPosition;
    // id = cursor.nodeId;
    // console.log(start, end)

    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);

    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);

    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);

    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);

    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);
    console.log("___ subelems")
    // Get sub elements.
    s1 = cursor.gotoFirstChild();
    console.log(cursor.nodeText);
    if(cursor.nodeText ==="Next"){
        console.log("NEXTNEXT");
    }
    console.log(cursor.nodeType);
    ident = get_ident_name(cursor);
    console.log(ident);
    cursor.gotoParent();


    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);
    ident = get_ident_name(cursor);
    console.log(ident);

    // Operator def.
    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);
    // Get sub elements.
    s1 = cursor.gotoFirstChild();
    console.log(cursor.nodeText);
    console.log(cursor.nodeType);
    ident = get_ident_name(cursor);
    console.log(ident);

    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);
    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);
    cursor.gotoParent();

    // Double line.
    s1 = cursor.gotoNextSibling();
    console.log(cursor.nodeType);
    return;
    
    
    // s1 = cursor.gotoFirstChild();
    // console.log(s1);
    // console.log(cursor.nodeType);

    // s1 = cursor.gotoFirstChild();
    // console.log(s1);
    // console.log(cursor.nodeType);
        
}

function evalNextBoundInfix(node, ctx){
    // lhs.
    let lhs = node.children[0];
    // symbol.
    let symbol = node.children[1];
    // console.log("symbol:", node.children[1]);
    // rhs
    let rhs = node.children[2];

    // Conjunction.
    if(symbol.type === "land"){
        console.log("###### LAND");
        console.log(node.text);
        // console.log("lhs:",node.children[0]);
        // console.log("rhs:",node.children[2]);
        // Evaluate each element of the conjunction list in order.
        // Recursively evaluate each child.
        let res;
        let out = ctx; //{"val": true, "states": vars};
        
        // lhs.
        let resLhs = evalNextExpr(node.children[0], ctx);
        console.log("resLhs:",resLhs)

        // rhs.
        let resRhs = evalNextExpr(node.children[2], resLhs);
        console.log("resRhs:",resRhs)

        return {"val": resLhs["val"] && resRhs["val"], "states": resRhs["states"]};
    }


    // Disjunction.
    if(symbol.type === "lor"){
        console.log("###### LOR");
        console.log("orig vars:", JSON.stringify(ctx["states"]));
        // For all existing possible variable assignments split into
        // separate evaluation cases for left and right branch.
        let ret = [lhs, rhs].map((c) => {
            evalNextExpr(c, ctx);
        })
        let retLhs = ret[0];
        let retRhs = ret[1];
        let boolVal = retLhs["val"] || retRhs["val"];
        if(!boolVal){
            return {"val": false, "states": []};
        }
        return {"val": boolVal, "states": retLhs["states"].concat(retRhs["states"])};



        let newLhsVars = _.flatten(ctx["states"].map(v => {
            return evalNextExpr(lhs, [v])["states"];
        }));
        console.log("newLhsVars: ", JSON.stringify(newLhsVars));

        let newRhsVars = _.flatten(ctx["states"].map(v => {
            return evalNextExpr(rhs, [v])["states"];
        }));
        console.log("newRhsVars: ", JSON.stringify(newRhsVars));

        return {"val": false, "states": newLhsVars.concat(newRhsVars)};
    }

    // Checks if a syntax tree node represents a primed variable.
    // TODO: Check for identifier in list of variables.
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

    // Equality.
    if(symbol.type ==="eq"){

        // Handle primed variable assignment.
        if(isPrimedVar(lhs)){
            console.log("bound_infix_op primed var, symbol: " + symbol.type);
    
            let rhsVal = evalNextExpr(rhs, ctx["states"]);
            let varName = lhs.children[0].text;
            let varNamePrimed = varName + "'";
            console.log("varNamePrimed:", varNamePrimed);
    
            // Update assignments for all possible variable assignments currently generated.
            let newVars = ctx["states"].map(function(v){
                return _.mapValues(v, (val,key,obj) => {
                    return (key === varNamePrimed) ? rhsVal : val;
                })
            })
    
            return {"val": true, "states": newVars}
        }
        
        // Handle unprimed variable assignment.
        if(!isPrimedVar(lhs) && lhs.type ==="identifier_ref"){
            // TODO: Don't update variable values here. Just compute
            // boolean value of equality expression.

            // Deal with equality of variable on left hand side.
            console.log("bound_infix_op, symbol: " + symbol.type);
            let rhsVal = evalNextExpr(rhs, ctx);
            console.log("rhsVal", rhsVal);
            let varName = lhs.text;

            // Update assignments for all possible variable assignments currently generated.
            let newVars = ctx["states"].filter((v) => {
                console.log(v);
                return v[varName] === rhsVal;
            })
            
            // map(function(v){

            //     if(v[varName] === rhsval){
            //         return val;
            //     } else{
            //         return null;
            //     }

            //     return _.mapValues(v, (val,key,obj) => {
            //         return (key === varName) ? rhsVal : val;
            //     })
            // })

            if(newVars.length === 0){
                return {"val": false, "states":[]};
            }

            return {"val": true, "states": newVars}
        }  
    }
}

// 'vars' is a list of possible partial state assignments known up to this point.
function evalInitBoundInfix(node, vars){
    // lhs.
    let lhs = node.children[0];
    // symbol.
    let symbol = node.children[1];
    // console.log("symbol:", node.children[1]);
    // rhs
    let rhs = node.children[2];

    // Disjunction.
    if(symbol.type === "lor"){
        // return {"val": false, "states": vars};
        console.log("###### LOR");
        console.log("orig vars:", JSON.stringify(vars));
        // For all existing possible variable assignments split into
        // separate evaluation cases for left and right branch.
        let newLhsVars = _.flatten(vars.map(v => {
            return evalInitExpr(lhs, [v])["states"];
        }));
        console.log("newLhsVars: ", JSON.stringify(newLhsVars));

        let newRhsVars = _.flatten(vars.map(v => {
            return evalInitExpr(rhs, [v])["states"];
        }));
        console.log("newRhsVars: ", JSON.stringify(newRhsVars));

        return {"val": false, "states": newLhsVars.concat(newRhsVars)};

    }

    // Equality.
    if(symbol.type ==="eq" && lhs.type ==="identifier_ref"){
        // Deal with equality of variable on left hand side.
        console.log("bound_infix_op, symbol: " + symbol.type);
        let rhsVal = evalInitExpr(rhs, vars);
        console.log("rhsVal", rhsVal);
        let varName = lhs.text;

        // Update assignments for all possible variable assignments currently generated.
        let newVars = vars.map(function(v){
            // If, in the current state assignment, the variable has not already
            // been assigned a value, then assign it.
            return _.mapValues(v, (val,key,obj) => {
                if(key === varName && val === null){
                    return rhsVal
                } else{
                    return val;
                }
            })
        })
        return {"val": false, "states": newVars}
    }    
}

// 'ctx' consists of the currently computed value of an expression and a 
// set of states generated by the expression evaluation so far i.e.
//  
//  {"val": curr_val, "states": [...]}
//
function evalNextExpr(node, ctx){
    if(node === undefined){
        return {"val": false, "states": []};
    }

    if(node.type === "disj_item"){
        console.log("disj_item, children:", node.children, ", ", node.text);
        disj_item_node = node.children[1];
        return evalNextExpr(disj_item_node, ctx);
    }

    if(node.type === "conj_item"){
        console.log("conj_item, children:", node.children, ", ", node.text);
        // console.log();
        // bullet_conj
        // console.log(node.children[0]);
        // console.log(node.children[0].type);
        // conj_item
        conj_item_node = node.children[1];
        return evalNextExpr(conj_item_node, ctx);
    }

    if(node.type === "conj_list"){
        console.log("conjunction list!");
        console.log("conjunction children:", node.children);
        // Evaluate each element of the conjunction list in order.
        // Recursively evaluate each child.
        let out = ctx; //{"val": true, "states": vars};
        for(const child of node.children){
            let res = evalNextExpr(child, out);
            out = {"val": out["val"] && res["val"], "states": res["states"]}
        }
        // If an expression evaluates to FALSE, then evaluation stops and no states are returned.
        if(!out["val"]){
            return {"val": false, "states": []};
        }
        return out;
    }  

    if(node.type === "disj_list"){
        console.log("disjunction list!");
        console.log("disjunction children:", node.children);
        let out = ctx; //{"val": true, "states": vars};

        out = []

        out = node.children.map(child => evalNextExpr(child, ctx));
        console.log("disj_list out:", out);
        // If an expression evaluates to FALSE, then evaluation stops and no states are returned.
        // if(!out["val"]){
            // return {"val": false, "states": []};
        // }
        return out;
    } 

    if(node.type === "bound_infix_op"){
        // console.log(node.type, "| ", node.text);
        return evalNextBoundInfix(node, ctx);
        console.log("new vars:", JSON.stringify(vars));
    }

    if(node.type === "identifier_ref"){
        //TODO.
        console.log(node.type);
        console.log(node.text);
    }
    if(node.type === "nat_number"){
        console.log(node.type, node.text);
        return parseInt(node.text);
        // return {"val": parseInt(node.text), "states": vars};
    }
}

// Evaluation of a TLC expression in the context of initial state generation
// can produce a few outcomes. Either, it simply updates the current assignment
// of values to variables, and/or it creates a new branch in the state computation,
// arising from presence of a disjunction (i.e. existential quantifier/set membership, etc.)
function evalInitExpr(node, vars){
    if(node === undefined){
        return {"val": false, "states": []};
    }
    if(node.type === "conj_list"){
        console.log("conjunction list!");
        console.log(node.children);
        // Evaluate each element of the conjunction list in order.
        // Recursively evaluate each child.
        let out = {"val": true, "states": vars};
        for(const child of node.children){
            let res = evalInitExpr(child, out["states"]);
            out = {"val": out["val"] && res["val"], "states": res["states"]}
        }
        return out;
    }  
    // if(node.type === "disj_list"){
    //     console.log("conjunction list!");
    //     console.log(node.children);
    //     // Evaluate each element of the conjunction list in order.
    //     // Recursively evaluate each child.
    //     for(const child of node.children){
    //         evalInitExpr(child, vars);
    //     }
    // }  
    if(node.type === "conj_item"){
        console.log(node.children);
        // bullet_conj
        console.log(node.children[0]);
        console.log(node.children[0].type);
        // conj_item
        conj_item_node = node.children[1];
        return evalInitExpr(conj_item_node, vars);
        // console.log(node.children[1]);
        // console.log(node.children[1].type);
        // console.log("conj_item");
    }
    if(node.type === "bound_infix_op"){
        console.log(node.type, "| ", node.text);
        return evalInitBoundInfix(node, vars);
        console.log("new vars:", JSON.stringify(vars));
    }

    if(node.type === "identifier_ref"){
        //TODO.
        console.log(node.type);
        console.log(node.text);
    }
    if(node.type === "nat_number"){
        console.log(node.type, node.text);
        return parseInt(node.text);
        // return {"val": parseInt(node.text), "states": vars};
    }
}

function getInitStates(initDef, vars){
    // Values of each state variable. Initially empty.
    init_var_vals = {};
    for(v in vars){
        init_var_vals[v] = null;
    }

    // var_vals = [init_var_vals]
    let var_vals = evalInitExpr(initDef, [init_var_vals]);
    console.log(var_vals);
    console.log("Possible initial state assignments:");
    for(const vars of var_vals["states"]){
        console.log(vars);
    }
    return var_vals["states"];
}

function getNextStates(nextDef, currStateVars){
    for(var k in currStateVars){
        let primedVar = k + "'";
        currStateVars[primedVar] = null;
    }
    console.log(currStateVars);
    ctx = {"val": true, "states": [currStateVars]}
    let ret = evalNextExpr(nextDef, ctx);
    console.log("getNextStates ret:", ret);
    // Only include evaluations that were TRUE.
    return ret.filter(c => c["val"]);
}


///////////////////////////////////////////////////
///////////////////////////////////////////////////
///////////////////////////////////////////////////


  async function handleLanguageChange() {
    const newLanguageName = languageSelect.value;
    if (!languagesByName[newLanguageName]) {
      const url = `${LANGUAGE_BASE_URL}/tree-sitter-${newLanguageName}.wasm`
      languageSelect.disabled = true;
      try {
        languagesByName[newLanguageName] = await TreeSitter.Language.load(url);
      } catch (e) {
        console.error(e);
        languageSelect.value = languageName;
        return
      } finally {
        languageSelect.disabled = false;
      }
    }

    tree = null;
    languageName = newLanguageName;
    parser.setLanguage(languagesByName[newLanguageName]);
    // handleCodeChange();
    // handleQueryChange();
    // \\/ x = 12
    // /\\ y = 3 \\/ y = 4
    // /\\ y = 3 /\\ y' = 13
    // VARIABLE y

    let newText = `----------------------- MODULE Test ------------------------
EXTENDS Naturals

VARIABLE x
VARIABLE y

Init == 
    /\\ x = 1 \\/ x = 2
    /\\ y = 3 \\/ y = 6

Next == 
    \\/ x = 1 /\\ x' = 99 /\\ y' = 88
    \\/ x = 2 /\\ x' = 209 /\\ y' = 288

=============================================================================`;
    newText = newText + "\n"

    console.log(newText);
    const newTree = parser.parse(newText, tree);
    console.log(newTree);
    tree = newTree;


    tlatext = document.getElementById('tlatext');
    tlatext.innerHTML = newText;

    lines = newText.split("\n");
    objs = walkTree(tree, lines);

    let vars = objs["var_decls"];
    let defns = objs["op_defs"];

    let initDef = defns["Init"];
    console.log("INIT:");
    console.log(initDef);
    console.log("initDef.childCount: ", initDef.childCount);
    console.log("initDef.type: ", initDef.type);

    let initStates = getInitStates(initDef, vars);

    let nextDef = defns["Next"];
    console.log("NEXT:");
    console.log(nextDef);
    console.log("nextDef.childCount: ", nextDef.childCount);
    console.log("nextDef.type: ", nextDef.type);

    // TODO: Implement this analogously to initial state generation.
    let currState = initStates[0];
    let allNextStates = []
    for(const state of initStates){
        console.log("$$$$$ Computing next states for current: " + JSON.stringify(state));
        let states = getNextStates(nextDef, currState);
        allNextStates = allNextStates.concat(states);
    }
    console.log(allNextStates);

    // Objects are passed by reference in JS.
    // D = {x: 1}
    // L = [1,[2,3],3]
    // function modify(o){
    //     o["x"] = 12;
    // }
    // function modifyL(lst){
    //     lst[1][0] = 55;
    // }
    // console.log(D);
    // modify(D);
    // console.log(D);


    // s1 = cursor.gotoNextSibling();
    // console.log(cursor.nodeType);
    // s1 = cursor.gotoNextSibling();
    // console.log(cursor.nodeType);
    // cursor.gotoParent();

    // s1 = cursor.gotoNextSibling();
    // console.log(cursor.nodeType);
    // // Get sub elements.
    // s1 = cursor.gotoFirstChild();
    // console.log(cursor.nodeText);
    // console.log(cursor.nodeType);
    // ident = get_ident_name(cursor);
    // console.log(ident);

    // s1 = cursor.gotoNextSibling();
    // console.log(cursor.nodeType);
    // s1 = cursor.gotoNextSibling();
    // console.log(cursor.nodeType);
    // cursor.gotoParent();

  }

  async function handleCodeChange(editor, changes) {
    const newText = codeEditor.getValue() + '\n';
    const edits = tree && changes && changes.map(treeEditForEditorChange);

    const start = performance.now();
    if (edits) {
      for (const edit of edits) {
        tree.edit(edit);
      }
    }
    const newTree = parser.parse(newText, tree);
    const duration = (performance.now() - start).toFixed(1);

    updateTimeSpan.innerText = `${duration} ms`;
    if (tree) tree.delete();
    tree = newTree;
    parseCount++;
    renderTreeOnCodeChange();
    runTreeQueryOnChange();
    saveStateOnChange();
  }

  async function renderTree() {
    isRendering++;
    const cursor = tree.walk();

    let currentRenderCount = parseCount;
    let row = '';
    let rows = [];
    let finishedRow = false;
    let visitedChildren = false;
    let indentLevel = 0;

    for (let i = 0;; i++) {
      if (i > 0 && i % 10000 === 0) {
        await new Promise(r => setTimeout(r, 0));
        if (parseCount !== currentRenderCount) {
          cursor.delete();
          isRendering--;
          return;
        }
      }

      let displayName;
      if (cursor.nodeIsMissing) {
        displayName = `MISSING ${cursor.nodeType}`
      } else if (cursor.nodeIsNamed) {
        displayName = cursor.nodeType;
      }

      if (visitedChildren) {
        if (displayName) {
          finishedRow = true;
        }

        if (cursor.gotoNextSibling()) {
          visitedChildren = false;
        } else if (cursor.gotoParent()) {
          visitedChildren = true;
          indentLevel--;
        } else {
          break;
        }
      } else {
        if (displayName) {
          if (finishedRow) {
            row += '</div>';
            rows.push(row);
            finishedRow = false;
          }
          const start = cursor.startPosition;
          const end = cursor.endPosition;
          const id = cursor.nodeId;
          let fieldName = cursor.currentFieldName();
          if (fieldName) {
            fieldName += ': ';
          } else {
            fieldName = '';
          }
          row = `<div>${'  '.repeat(indentLevel)}${fieldName}<a class='plain' href="#" data-id=${id} data-range="${start.row},${start.column},${end.row},${end.column}">${displayName}</a> [${start.row}, ${start.column}] - [${end.row}, ${end.column}]`;
          finishedRow = true;
        }

        if (cursor.gotoFirstChild()) {
          visitedChildren = false;
          indentLevel++;
        } else {
          visitedChildren = true;
        }
      }
    }
    if (finishedRow) {
      row += '</div>';
      rows.push(row);
    }

    cursor.delete();
    cluster.update(rows);
    treeRows = rows;
    isRendering--;
    handleCursorMovement();
  }

  function runTreeQuery(_, startRow, endRow) {
    if (endRow == null) {
      const viewport = codeEditor.getViewport();
      startRow = viewport.from;
      endRow = viewport.to;
    }

    codeEditor.operation(() => {
      const marks = codeEditor.getAllMarks();
      marks.forEach(m => m.clear());

      if (tree && query) {
        const captures = query.captures(
          tree.rootNode,
          {row: startRow, column: 0},
          {row: endRow, column: 0},
        );
        let lastNodeId;
        for (const {name, node} of captures) {
          if (node.id === lastNodeId) continue;
          lastNodeId = node.id;
          const {startPosition, endPosition} = node;
          codeEditor.markText(
            {line: startPosition.row, ch: startPosition.column},
            {line: endPosition.row, ch: endPosition.column},
            {
              inclusiveLeft: true,
              inclusiveRight: true,
              css: `color: ${colorForCaptureName(name)}`
            }
          );
        }
      }
    });
  }

  function handleQueryChange() {
    if (query) {
      query.delete();
      query.deleted = true;
      query = null;
    }

    queryEditor.operation(() => {
      queryEditor.getAllMarks().forEach(m => m.clear());
      if (!queryCheckbox.checked) return;

      const queryText = queryEditor.getValue();

      try {
        query = parser.getLanguage().query(queryText);
        let match;

        let row = 0;
        queryEditor.eachLine((line) => {
          while (match = CAPTURE_REGEX.exec(line.text)) {
            queryEditor.markText(
              {line: row, ch: match.index},
              {line: row, ch: match.index + match[0].length},
              {
                inclusiveLeft: true,
                inclusiveRight: true,
                css: `color: ${colorForCaptureName(match[1])}`
              }
            );
          }
          row++;
        });
      } catch (error) {
        const startPosition = queryEditor.posFromIndex(error.index);
        const endPosition = {
          line: startPosition.line,
          ch: startPosition.ch + (error.length || Infinity)
        };

        if (error.index === queryText.length) {
          if (startPosition.ch > 0) {
            startPosition.ch--;
          } else if (startPosition.row > 0) {
            startPosition.row--;
            startPosition.column = Infinity;
          }
        }

        queryEditor.markText(
          startPosition,
          endPosition,
          {
            className: 'query-error',
            inclusiveLeft: true,
            inclusiveRight: true,
            attributes: {title: error.message}
          }
        );
      }
    });

    runTreeQuery();
    saveQueryState();
  }

  function handleCursorMovement() {
    if (isRendering) return;

    const selection = codeEditor.getDoc().listSelections()[0];
    let start = {row: selection.anchor.line, column: selection.anchor.ch};
    let end = {row: selection.head.line, column: selection.head.ch};
    if (
      start.row > end.row ||
      (
        start.row === end.row &&
        start.column > end.column
      )
    ) {
      let swap = end;
      end = start;
      start = swap;
    }
    const node = tree.rootNode.namedDescendantForPosition(start, end);
    if (treeRows) {
      if (treeRowHighlightedIndex !== -1) {
        const row = treeRows[treeRowHighlightedIndex];
        if (row) treeRows[treeRowHighlightedIndex] = row.replace('highlighted', 'plain');
      }
      treeRowHighlightedIndex = treeRows.findIndex(row => row.includes(`data-id=${node.id}`));
      if (treeRowHighlightedIndex !== -1) {
        const row = treeRows[treeRowHighlightedIndex];
        if (row) treeRows[treeRowHighlightedIndex] = row.replace('plain', 'highlighted');
      }
      cluster.update(treeRows);
      const lineHeight = cluster.options.item_height;
      const scrollTop = outputContainerScroll.scrollTop;
      const containerHeight = outputContainerScroll.clientHeight;
      const offset = treeRowHighlightedIndex * lineHeight;
      if (scrollTop > offset - 20) {
        $(outputContainerScroll).animate({scrollTop: offset - 20}, 150);
      } else if (scrollTop < offset + lineHeight + 40 - containerHeight) {
        $(outputContainerScroll).animate({scrollTop: offset - containerHeight + 40}, 150);
      }
    }
  }

  function handleTreeClick(event) {
    if (event.target.tagName === 'A') {
      event.preventDefault();
      const [startRow, startColumn, endRow, endColumn] = event
        .target
        .dataset
        .range
        .split(',')
        .map(n => parseInt(n));
      codeEditor.focus();
      codeEditor.setSelection(
        {line: startRow, ch: startColumn},
        {line: endRow, ch: endColumn}
      );
    }
  }

  function handleLoggingChange() {
    if (loggingCheckbox.checked) {
      parser.setLogger((message, lexing) => {
        if (lexing) {
          console.log("  ", message)
        } else {
          console.log(message)
        }
      });
    } else {
      parser.setLogger(null);
    }
  }

  function handleQueryEnableChange() {
    if (queryCheckbox.checked) {
      queryContainer.style.visibility = '';
      queryContainer.style.position = '';
    } else {
      queryContainer.style.visibility = 'hidden';
      queryContainer.style.position = 'absolute';
    }
    handleQueryChange();
  }

  function treeEditForEditorChange(change) {
    const oldLineCount = change.removed.length;
    const newLineCount = change.text.length;
    const lastLineLength = change.text[newLineCount - 1].length;

    const startPosition = {row: change.from.line, column: change.from.ch};
    const oldEndPosition = {row: change.to.line, column: change.to.ch};
    const newEndPosition = {
      row: startPosition.row + newLineCount - 1,
      column: newLineCount === 1
        ? startPosition.column + lastLineLength
        : lastLineLength
    };

    const startIndex = codeEditor.indexFromPos(change.from);
    let newEndIndex = startIndex + newLineCount - 1;
    let oldEndIndex = startIndex + oldLineCount - 1;
    for (let i = 0; i < newLineCount; i++) newEndIndex += change.text[i].length;
    for (let i = 0; i < oldLineCount; i++) oldEndIndex += change.removed[i].length;

    return {
      startIndex, oldEndIndex, newEndIndex,
      startPosition, oldEndPosition, newEndPosition
    };
  }

  function colorForCaptureName(capture) {
    const id = query.captureNames.indexOf(capture);
    return COLORS_BY_INDEX[id % COLORS_BY_INDEX.length];
  }

  function loadState() {
    const language = localStorage.getItem("language");
    const sourceCode = localStorage.getItem("sourceCode");
    const query = localStorage.getItem("query");
    const queryEnabled = localStorage.getItem("queryEnabled");
    if (language != null && sourceCode != null && query != null) {
      queryInput.value = query;
      codeInput.value = sourceCode;
      languageSelect.value = language;
      queryCheckbox.checked = (queryEnabled === 'true');
    }
  }

  function saveState() {
    localStorage.setItem("language", languageSelect.value);
    localStorage.setItem("sourceCode", codeEditor.getValue());
    saveQueryState();
  }

  function saveQueryState() {
    localStorage.setItem("queryEnabled", queryCheckbox.checked);
    localStorage.setItem("query", queryEditor.getValue());
  }

  function debounce(func, wait, immediate) {
    var timeout;
    return function() {
      var context = this, args = arguments;
      var later = function() {
        timeout = null;
        if (!immediate) func.apply(context, args);
      };
      var callNow = immediate && !timeout;
      clearTimeout(timeout);
      timeout = setTimeout(later, wait);
      if (callNow) func.apply(context, args);
    };
  }
})();
