let tree;

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
  const parser = new TreeSitter();

  let tree = null;

  var ASSIGN_PRIMED = false;

  const codeEditor = CodeMirror.fromTextArea(codeInput, {
    lineNumbers: true,
    showCursorWhenSelecting: true
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
    let specPath = "./specs/lockserver_nodefs.tla";
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

  function genRandTrace(){
    
    // Pick a random element from the given array.
    function randChoice(arr){
        let randI = _.random(0, arr.length-1);
        return arr[randI];
    }


    const newText = codeEditor.getValue() + '\n';
    const newTree = parser.parse(newText, tree);

    objs = walkTree(newTree);
    let vars = objs["var_decls"];
    let defns = objs["op_defs"];

    let initDef = defns["Init"];
    let nextDef = defns["Next"];

    let initStates = getInitStates(initDef, vars);
    initStates = initStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);

    // Pick a random initial state.
    let currState = randChoice(initStates);
    console.log("initState in trace:", currState);

    let max_trace_depth = 6;
    let curr_depth = 0;
    let trace = [_.cloneDeep(currState)];
    while(curr_depth < max_trace_depth){
        // Get next states from the current state and pick a random one.
        let nextStates = getNextStates(nextDef, currState);
        nextStates = nextStates.filter(ctx => ctx["val"]).map(ctx => ctx["state"]);
        // console.log(nextStates);
        let nextState = _.cloneDeep(randChoice(nextStates));
        // Rename primed variables to unprimed variables.
        nextState = _.pickBy(nextState, (val,k,obj) => k.endsWith("'"));
        nextState = _.mapKeys(nextState, (val,k,obj) => k.slice(0,k.length-1));
        console.log(nextState);
        // Process next state.
        currState = nextState;
        curr_depth += 1;
        trace.push(_.cloneDeep(currState));
    }

    // Display trace.
    let traceDiv = document.getElementById("trace");
    traceDiv.innerHTML = "";
    console.log(trace);
    let stateInd = 0;
    for(const state of trace){
        traceDiv.innerHTML += "<div>";
        traceDiv.innerHTML += "<h3>State " + stateInd + "</h3>"
        console.log(state);
        for(const varname in state){
            traceDiv.innerHTML += "<span>" + varname +":"+ JSON.stringify(state[varname]) + "</span>";
            traceDiv.innerHTML += "<br>"
        }
        traceDiv.innerHTML += "</div>";
        stateInd += 1;
    }
    traceDiv.innerHTML += "<br><br>";
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

    console.log("Re-generating states.");
    let res = generateStates(newTree);

    // Display states in HTML.
    let initStatesDiv = document.getElementById("initial-states");
    initStatesDiv.innerHTML = "";
    for(const state of res["initStates"]){
        initStatesDiv.innerHTML += "<div>" + JSON.stringify(state) + "</div>";
    }

    // let nextStatesDiv = document.getElementById("next-states");
    // nextStatesDiv.innerHTML = "";
    // for(const ctx of res["nextStates"]){
    //     if(ctx["val"]){
    //         nextStatesDiv.innerHTML += "<div>" + JSON.stringify(ctx["state"]) + "</div>";
    //     }
    // }
    genRandTrace();
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
