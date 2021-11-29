//
// Test script runs on 'test.html' page.
//

let tree;

(async () => {

    // Set up parser.
    await TreeSitter.init();
    const parser = new TreeSitter();

    const newLanguageName = "tlaplus";
    const url = `${LANGUAGE_BASE_URL}/tree-sitter-${newLanguageName}.wasm`
    let lang = await TreeSitter.Language.load(url);
    parser.setLanguage(lang);

    let tree = null;

    function testStateGen(testId, specText, initExpected){
        let div;
        tree = null;
        const newTree = parser.parse(specText + "\n", tree);
        let ret = generateStates(newTree);
        const pass = _.isEqual(ret["initStates"], initExpected);
    
        let testHeader = document.createElement("h2");
        testHeader.innerText = "Test: " + testId + "";
        let specCode = document.createElement("code");
        specCode.innerText = specText;
        testsDiv.appendChild(testHeader);
        testsDiv.appendChild(specCode);

        // Print expected initial states.
        div = document.createElement("div");
        div.innerText = "Expected initial states:"
        testsDiv.appendChild(div);
        for(const state of initExpected){
            let stateDiv = document.createElement("div");
            stateDiv.innerText = JSON.stringify(state);
            testsDiv.appendChild(stateDiv);
        }

        // Print generated initial states.
        div = document.createElement("div");
        div.innerText = "Initial states:"
        testsDiv.appendChild(div);
        for(const state of ret["initStates"]){
            let stateDiv = document.createElement("div");
            stateDiv.innerText = JSON.stringify(state);
            testsDiv.appendChild(stateDiv);
        }

        let statusText = pass ? "PASS &#10003" : "FAIL &#10007";
        let statusColor = pass ? "green" : "red";
        div = document.createElement("div");
        div.innerHTML = statusText;
        div.style = "font-weight: bold; color:" + statusColor;
        testsDiv.appendChild(div);
    }

    let testsDiv = document.getElementById("tests");
    let initExpected;

    let spec1 = `----------------------- MODULE Test ------------------------
VARIABLE x
Init == x = 1 
Next == x' = 2
=============================================================================`;
initExpected = [{x:1}];
testStateGen("simple-spec1", spec1, initExpected);

let spec2 = `----------------------- MODULE Test ------------------------
VARIABLE x
Init == x = 1 \\/ x = 2 
Next == x' = 2
=============================================================================`;
initExpected = [{x:1}, {x:2}];    
testStateGen("simple-spec2", spec2, initExpected);

let spec3 = `----------------------- MODULE Test ------------------------
VARIABLE x
VARIABLE y
Init == 
    /\\ x = 1 \\/ x = 2 
    /\\ y = 3 \\/ y = 4

Next == x' = 2 /\\ y' = 2
=============================================================================`;
// TODO: The expected value comparisons shouldn't be dependent on the order of
// the returned states.
initExpected = [{x:1,y:3},{x:2,y:3},{x:1,y:4},{x:2,y:4}];    
testStateGen("simple-spec3", spec3, initExpected);

    

})();