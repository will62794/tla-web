let tree;
let allInitStates = [];
let nextStatePred = null;
let currState = null;
let currNextStates = [];
let currTrace = []
let currTraceAliasVals = []
let specTreeObjs = null;
let specDefs = null;
let specConsts = null;
let specConstVals = {};
let parser;

// Parse URL params;
const urlSearchParams = new URLSearchParams(window.location.search);
const urlParams = Object.fromEntries(urlSearchParams.entries());
let enableEvalTracing = parseInt(urlParams["debug"]);

// TODO: Implement this properly.
function toggleSpec(){
    let pane = document.getElementById("input-pane");
    pane.style.width="0%";
}

function renderNextStateChoices(nextStates){
    let initStatesDiv = document.getElementById("initial-states");
    initStatesDiv.innerHTML = "";
    // initStatesDiv.innerHTML += "<div>"
    for(const state of nextStates){
        let stateDiv = document.createElement("div");
        stateDiv.classList.add("init-state");
        // console.log("render next:", state);
        for(const varname in state.getStateObj()){
            stateDiv.innerHTML += `<span class='state-varname'>${varname}</span> = `
            // stateDiv.innerHTML += JSON.stringify(state[varname]);
            stateDiv.innerHTML += state.getVarVal(varname);
            stateDiv.innerHTML += "<br>"
        }
        let hash = hashSum(state);
        stateDiv.setAttribute("onclick", `handleChooseState("${hash}")`);
        initStatesDiv.appendChild(stateDiv);
    }
}

// Step back one state in the current trace.
function traceStepBack(){
    currTrace = currTrace.slice(0, currTrace.length - 1);
    // Step back in alias trace as well.
    if(currTraceAliasVals.length > 0){
        currTraceAliasVals = currTraceAliasVals.slice(0, currTraceAliasVals.length - 1);
    }
    // Back to initial states.
    if(currTrace.length === 0){
        console.log("Back to initial states.")
        reloadSpec();
        return;
    } else{
        console.log("stepping back");
        let lastState = currTrace[currTrace.length-1];
        let interp = new TlaInterpreter();
        let nextStates = interp.computeNextStates(specTreeObjs, specConstVals, [_.cloneDeep(lastState)])
                            .map(c => c["state"].deprimeVars());
        currNextStates = _.cloneDeep(nextStates);
        renderNextStateChoices(currNextStates);
        renderCurrentTrace();
    }
}

function updateTraceLink(){
    var url_ob = new URL(document.URL);
    var traceHashes = currTrace.map(s => hashSum(s));
    console.log(traceHashes);
    url_ob.hash = '#' + traceHashes.join(",");

    // Save the trace as a comma separated list of short state hashes.
    var new_url = url_ob.href;
    document.location.href = new_url;
}

// Save the current trace in the URL.
function traceGetLink(){
    if(currTrace.length === 0){
        return;
    }
    updateTraceLink();
}

// Load a trace from URL link. Returns false if there is no link to load.
function loadTraceFromLink(){
    var url_ob = new URL(document.URL);
    console.log("URL hash:", url_ob.hash);
    if(url_ob.hash <= 1){
        return false;
    }
    var traceHashes = url_ob.hash.slice(1).split(",");
    console.log(traceHashes);

    for(var ind=0;ind<traceHashes.length;ind++){
        let shortHash = traceHashes[ind];
        handleChooseState(shortHash)
    }

    return true;
    // url_ob.hash = '#' + traceHashes.join(",");

    // Save the trace as a comma separated list of short state hashes
    // var new_url = url_ob.href;
    // document.location.href = new_url;
}

function renderCurrentTrace(){
    let traceDiv = document.getElementById("trace");
    traceDiv.innerHTML = "";
    console.log(trace);
    let stateInd = 0;
    let hasAliasVals = (currTraceAliasVals.length > 0);
    for(var ind=0;ind < currTrace.length;ind++){
        let state = currTrace[ind];
        let stateAliasVal = null;
        if(hasAliasVals){
            stateAliasVal = currTraceAliasVals[ind];
        }
        let isLastState = ind === currTrace.length - 1;
        let traceStateDiv = document.createElement("div");
        // traceStateDiv.innerHTML += "<b>State " + stateInd + "</b><br>"
        traceStateDiv.classList.add("trace-state");
        // console.log("trace state:", state);
        for(const varname in state.getStateObj()){
            traceStateDiv.innerHTML += "<span><span class='state-varname'>" + varname +"</span> = "+ state.getVarVal(varname) + "</span>";
            traceStateDiv.innerHTML += "<br>"
        }
        // Append Alias if needed.
        if(hasAliasVals){
            let aliasVarName = "Alias"
            traceStateDiv.innerHTML += "<span class='alias-var'><span class='state-varname'>" + aliasVarName +"</span> = "+ stateAliasVal + "</span>";
            traceStateDiv.innerHTML += "<br>"
        }

        traceDiv.appendChild(traceStateDiv);
        stateInd += 1;
    }
    traceDiv.innerHTML += "<br><br>";
    
    let header = document.getElementById("poss-next-states-title");
    header.innerHTML = (currTrace.length > 0) ? "Choose Next State" : "Choose Initial State";

    updateTraceLink();

}

function handleChooseState(statehash_short){
    // console.log("currNextStates:", JSON.stringify(currNextStates));
    let nextStateChoices = currNextStates.filter(s => hashSum(s)===statehash_short);
    if(nextStateChoices.length === 0){
        throw Error("Given state hash does not exist among possible next states.")
    }
    let nextState = nextStateChoices[0];

    // Compute ALIAS value if one exists.
    let aliasVal = null;
    if(specAlias !== undefined){
        let initCtx = new Context(null, nextState, specDefs, {}, specConsts);
        let aliasNode = specAlias.node
        aliasVal = evalExpr(aliasNode, initCtx)[0]["val"];
        console.log("aliasVal:", aliasVal);
        currTraceAliasVals.push(aliasVal);
    }

    // TODO: Consider detecting cycles in the trace.
    currTrace.push(nextState);
    console.log("nextState:", JSON.stringify(nextState));
    console.log("nextStatePred:", nextStatePred);
    const start = performance.now();

    let interp = new TlaInterpreter();

    try {
        let nextStates = interp.computeNextStates(specTreeObjs, specConstVals, [nextState])
            .map(c => c["state"].deprimeVars());
        currNextStates = _.cloneDeep(nextStates);
        const duration = (performance.now() - start).toFixed(1);
        console.log(`Generation of next states took ${duration}ms`)
    } catch (e) {
        console.error("Error computing next states.");
        if (currEvalNode !== null) {
            // Display line where evaluation error occurred.
            // TODO: Need to update this to map back to original line before we desugared.
            const $codeEditor = document.querySelector('.CodeMirror');
            let errorLine = currEvalNode["startPosition"]["row"];
            $codeEditor.CodeMirror.addLineClass(errorLine, 'background', 'line-error');
            $codeEditor.CodeMirror.scrollIntoView(errorLine, 200);
            console.log("error evaluating node: ", currEvalNode);
            console.log(e);
        }
        return;
    }

    // Re-render.
    renderCurrentTrace();
    renderNextStateChoices(currNextStates);
}

function setConstantValues(){
    let constVals = {};
    let nullTree;
    for(var constDecl in specConsts){
        let inputElem = document.getElementById("const-val-input-" + constDecl);
        let constValText = inputElem.value;
        console.log(constDecl, constValText);
        constVals[constDecl] = constValText;
    }

    // Create a dummy spec to evaluate the expressions given for each CONSTANT.
    // TODO: Might be a simpler way to do this TLA+ expression evaluation.
    let dummySpec = "---- MODULE simple_lockserver_with_constants ----\n";
    for(var constDecl in specConsts){
        dummySpec += `${constDecl} == ${constVals[constDecl]}\n`;
    }
    for(var constDecl in specConsts){
        dummySpec += `VARIABLE var_${constDecl}\n`;
    }
    dummySpec += `Init == \n`;
    for(var constDecl in specConsts){
        dummySpec += `/\\ var_${constDecl} = ${constDecl}\n`;
    }
    dummySpec += `Next == \n`;
    for(var constDecl in specConsts){
        dummySpec += `/\\ var_${constDecl}' = var_${constDecl}\n`;
    }

    console.log(dummySpec);

    dummySpec += "====";

    const dummySpecTree = parser.parse(dummySpec, nullTree);
    console.log(dummySpecTree);

    let dummyTreeObjs = parseSpec(dummySpec);
    console.log(dummyTreeObjs);

    // TODO: Make sure we evaluate the expression we're assigning to a constant
    // value first.

    // Compute the single initial state.
    let interp = new TlaInterpreter();
    let dummyInitStates = interp.computeInitStates(dummyTreeObjs);
    console.log("dummy init states:", dummyInitStates);
    assert(dummyInitStates.length === 1);
    let initStateEval = dummyInitStates[0];
    let constTlaVals = {};
    for(var constDecl in specConsts){
        constTlaVals[constDecl] = initStateEval.getVarVal(`var_${constDecl}`);
    }

    // TODO: Thread these assigned values through standard spec evaluation.
    console.log("constTlaVals:", constTlaVals);
    specConstVals = constTlaVals;

    reloadSpec();
}

// TODO: Simple reachability benchmark that can eventually be incorporated into 
// benchmarks page.
function reachableBench(){
    let start  = performance.now();
    let reachable = computeReachableStates(specTreeObjs, specConstVals)["states"];
    const duration = (performance.now() - start).toFixed(1);
    console.log(`Computed ${reachable.length} reachable states in ${duration}ms.`);
}

/**
 * Clear the current trace, re-parse the spec and generate initial states.
 */
function reloadSpec(){
    console.log("Clearing current trace.");
    currTrace = []
    currTraceAliasVals = []
    renderCurrentTrace();

    console.log("Generating initial states.");
    let interp = new TlaInterpreter();
    let allInitStates;
    let initStates;
    try{
      initStates = interp.computeInitStates(specTreeObjs, specConstVals);
      allInitStates = _.cloneDeep(initStates);
      console.log("Set initial states: ", allInitStates);
    } catch(e){
      console.error("Error computing initial states.");
      if(currEvalNode !== null){
        // Display line where evaluation error occurred.
        const $codeEditor = document.querySelector('.CodeMirror');
        // console.log(currEvalNode["startPosition"]);
        // console.log(currEvalNode["endPosition"]);

        let errorLine = currEvalNode["startPosition"]["row"];
        $codeEditor.CodeMirror.addLineClass(errorLine, 'background', 'line-error');
        console.log("error evaluating node: ", currEvalNode);
        console.log(e);
      }
      return;
    }

    console.log("Computed " + allInitStates.length + " initial states.");
    
    // Display states in HTML.
    let initStatesDiv = document.getElementById("initial-states");
    initStatesDiv.innerHTML = "";
    renderNextStateChoices(initStates);
    console.log("Rendered initial states");

    currNextStates = _.cloneDeep(initStates);

    // Check for trace to load from given link.
    // loadTraceFromLink();
    // displayStateGraph();
}

function displayStateGraph(){
    //
    // TODO: Will need to flesh out this functionality further.
    //

    let stategraphDiv = document.getElementById('stategraph');
    stategraphDiv.hidden = false;
    
    var cy = cytoscape({
        container: document.getElementById('stategraph'), // container to render in
        style: [
            {
              selector: 'node',
              style: {
                'label': function(el){
                    return JSON.stringify(el.data()["state"]);
                },
                "background-color": "lightgray",
                "border-style": "solid",
                "border-width": "1",
                "border-color": "black"
              }
            },
          ]
    });

    let reachable = computeReachableStates(specTreeObjs, specConstVals);
    let edges = reachable["edges"];
    console.log(reachable["edges"]);
    console.log(reachable);

    for(const state of reachable["states"]){
        dataVal = {id: hashSum(state), state: state};
        console.log(dataVal);
        cy.add({
            group: 'nodes',
            data: dataVal,
            position: { x: 200, y: 200 }
        });
    }

    let eind = 0;
    for(const edge of edges){
        cy.add({
            group: 'edges', data: { 
                id: 'e' + eind, 
                source: hashSum(edge[0]), 
                target: hashSum(edge[1]) 
            }
        });
        eind++;
    }
    cy.edges('edge').style({
        "curve-style": "straight",
        "target-arrow-shape": "triangle"
    })
    // let layout = cy.layout({name:"cose"});
    let layout = cy.layout({name:"breadthfirst"});
    layout.run();
}

(async () => {

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
  parser = new TreeSitter();

  let tree = null;

  var ASSIGN_PRIMED = false;

  const codeEditor = CodeMirror.fromTextArea(codeInput, {
    lineNumbers: true,
    showCursorWhenSelecting: true,
    // TODO: Work out tlaplus mode functionality for syntax highlighting.
    // mode:"tlaplus"
  });

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

  codeEditor.on('changes', handleCodeChange);
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

    // Download example spec.
    // let specPath = "./specs/simple1.tla";
    // let specPath = "./specs/simple2.tla";
    // let specPath = "./specs/lockserver.tla";
    // let specPath = "./specs/LamportMutex.tla";
    let specPath = "./specs/lockserver_nodefs.tla";
    // let specPath = "./specs/MongoLoglessDynamicRaft.tla";
    // let specPath = "./specs/Paxos.tla";
    // let specPath = "./specs/simple_test.tla";
    // let specPath = "./specs/simple_lockserver.tla";

    // Check for given spec in URL args.
    specPathArg = urlParams["specpath"];

    // Load given spec.
    if(specPathArg !== undefined){
        specPath = specPathArg;
    }


    (() => {
        const handle = setInterval(() => {
            res = $.get(specPath, data => {
                const $codeEditor = document.querySelector('.CodeMirror');
                spec = data;
                console.log("Retrieved spec:", specPath);
                if ($codeEditor) {
                    // code change handler should be triggered when we update the code mirror text.
                    $codeEditor.CodeMirror.setValue(spec);
                    $codeEditor.CodeMirror.setSize("100%", "100%");
                    clearInterval(handle);
                    // handleCodeChange();
                }
            });
        }, 500);
    })();
  }

//   function genRandTrace(){
    
//     // Pick a random element from the given array.
//     function randChoice(arr){
//         let randI = _.random(0, arr.length-1);
//         return arr[randI];
//     }


//     const newText = codeEditor.getValue() + '\n';
//     const newTree = parser.parse(newText, tree);

//     objs = OLD(newTree);
//     let vars = objs["var_decls"];
//     let defns = objs["op_defs"];

//     let initDef = defns["Init"];
//     let nextDef = defns["Next"];

//     let initStates = getXXXusenewmethodhereXXXStates(initDef, vars);
//     initStates = initStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);

//     // Pick a random initial state.
//     let currState = randChoice(initStates);
//     console.log("initState in trace:", currState);

//     let max_trace_depth = 6;
//     let curr_depth = 0;
//     let trace = [_.cloneDeep(currState)];
//     while(curr_depth < max_trace_depth){
//         // Get next states from the current state and pick a random one.
//         let nextStates = getXXXupdateifneededXXXStates(nextDef, currState);
//         nextStates = nextStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);
//         // console.log(nextStates);
//         let nextState = _.cloneDeep(randChoice(nextStates));
//         // Rename primed variables to unprimed variables.
//         nextState = _.pickBy(nextState, (val,k,obj) => k.endsWith("'"));
//         nextState = _.mapKeys(nextState, (val,k,obj) => k.slice(0,k.length-1));
//         console.log(nextState);
//         // Process next state.
//         currState = nextState;
//         curr_depth += 1;
//         trace.push(_.cloneDeep(currState));
//     }

//     // Display trace.
//     let traceDiv = document.getElementById("trace");
//     traceDiv.innerHTML = "";
//     console.log(trace);
//     let stateInd = 0;
//     for(const state of trace){
//         traceDiv.innerHTML += "<div>";
//         traceDiv.innerHTML += "<b>State " + stateInd + "</b>"
//         console.log(state);
//         for(const varname in state){
//             traceDiv.innerHTML += "<span>" + varname +": "+ JSON.stringify(state[varname]) + "</span>";
//             traceDiv.innerHTML += "<br>"
//         }
//         traceDiv.innerHTML += "</div>";
//         stateInd += 1;
//     }
//     traceDiv.innerHTML += "<br><br>";
//   }

  async function handleCodeChange(editor, changes) {

    // Remove any existing line error highlights.
    var nlines = codeEditor.lineCount();
    for (var i = 0; i < nlines; i++) {
      codeEditor.removeLineClass(i, "background");
    }

    const newText = codeEditor.getValue() + '\n';
    const edits = tree && changes && changes.map(treeEditForEditorChange);

    const start = performance.now();
    if (edits) {
      for (const edit of edits) {
        tree.edit(edit);
      }
    }
    specTreeObjs = parseSpec(newText);

    specConsts = specTreeObjs["const_decls"];
    specDefs = specTreeObjs["op_defs"];
    nextStatePred = specTreeObjs["op_defs"]["Next"]["node"];
    specAlias = specTreeObjs["op_defs"]["Alias"];

    // If there are CONSTANT declarations in the spec, we must
    // instantiate them with some concrete values.
    if(!_.isEmpty(specConsts)){
        console.log("Instantiating spec constants.");

        let chooseConstsContainer = document.getElementById("choose-constants-container");
        chooseConstsContainer.innerHTML = "";
        let chooseTitle = document.createElement("div");
        chooseTitle.innerHTML = "Choose constants";
        chooseTitle.classList.add("pane-title");
        chooseConstsContainer.appendChild(chooseTitle);

        let chooseConstsElem = document.createElement("div");
        chooseConstsElem.id = "choose-constants-elems";
        for(const constDecl in specConsts){
            console.log(constDecl);
            let newDiv = document.createElement("div");
            newDiv.innerHTML = "CONSTANT " + constDecl + " &#8592; ";
            newDiv.innerHTML += `<input class='const-input' id='const-val-input-${constDecl}'>`;
            chooseConstsElem.appendChild(newDiv);
        }

        let setButtonDiv = document.createElement("div");
        setButtonDiv.innerHTML = "Set constant values"
        setButtonDiv.id = "set-constants-button"        
        setButtonDiv.classList.add("button-base");     
        setButtonDiv.setAttribute("onclick", 'setConstantValues()');
        chooseConstsElem.appendChild(setButtonDiv);

        chooseConstsContainer.appendChild(chooseConstsElem);

        // Don't try to reload the spec if we have to instantiate constants.
        return;
    }

    const duration = (performance.now() - start).toFixed(1);


    reloadSpec();

    // // TODO: Consider what occurs when spec code changes after the
    // // initial page load.
    // console.log("Generating initial states.");
    // let initStates = computeInitStates(specTreeObjs, specConstVals);
    // allInitStates = initStates;

    // // Display states in HTML.
    // let initStatesDiv = document.getElementById("initial-states");
    // initStatesDiv.innerHTML = "";
    // renderNextStateChoices(initStates);
    // console.log("Rendered initial states");

    // currNextStates = _.cloneDeep(initStates);

    // // Check for trace to load from given link.
    // loadTraceFromLink();
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
