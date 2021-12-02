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

    // Do two arrays (treated as sets) contain the same elements.
    function arrEq(a1,a2){
        let a1Uniq = _.uniqWith(a1, _.isEqual)
        let a2Uniq = _.uniqWith(a2, _.isEqual)

        let sameSize = a1Uniq.length === a2Uniq.length;
        let sameEls = _.every(a1Uniq, (s) => _.find(a2Uniq, t => _.isEqual(s,t)));
        return sameSize && sameEls;
    }

    function testStateGen(testId, specText, initExpected, nextExpected){
        let div;
        tree = null;
        const newTree = parser.parse(specText + "\n", tree);
        let ret = generateStates(newTree);
        
        // Test correct initial states.
        let initStates = ret["initStates"]
        const passInit = arrEq(initExpected, initStates);

        // Test correct next states.
        let nextStates = ret["nextStates"].map(c => c["state"]);
        const passNext = arrEq(nextExpected, nextStates);

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

        // Print expected next states.
        div = document.createElement("div");
        div.innerText = "Expected next states:"
        testsDiv.appendChild(div);
        for(const state of nextExpected){
            let stateDiv = document.createElement("div");
            stateDiv.innerText = JSON.stringify(state);
            testsDiv.appendChild(stateDiv);
        }

        // Print next states.
        div = document.createElement("div");
        div.innerText = "Next states:"
        testsDiv.appendChild(div);
        for(const state of nextStates){
            let stateDiv = document.createElement("div");
            stateDiv.innerText = JSON.stringify(state);
            testsDiv.appendChild(stateDiv);
        }

        let statusText = "Init: " + (passInit ? "PASS &#10003" : "FAIL &#10007");
        let statusColor = passInit ? "green" : "red";
        div = document.createElement("div");
        div.innerHTML = statusText;
        div.style = "font-weight: bold; color:" + statusColor;
        testsDiv.appendChild(div);

        statusText = "Next: " + (passNext ? "PASS &#10003" : "FAIL &#10007");
        statusColor = passNext ? "green" : "red";
        div = document.createElement("div");
        div.innerHTML = statusText;
        div.style = "font-weight: bold; color:" + statusColor;
        testsDiv.appendChild(div);
    }



let testsDiv = document.getElementById("tests");
let initExpected;
let nextExpected;

function simple_spec1(){
    let spec1 = `----------------------- MODULE Test ------------------------
    VARIABLE x
    Init == x = 1 
    Next == x' = 2
    ====`;
    initExpected = [{x:1}];
    nextExpected = [{"x":1, "x'":2}]
    testStateGen("simple-spec1", spec1, initExpected, nextExpected);
}

function simple_spec2(){
    let spec2 = `----------------------- MODULE Test ------------------------
    VARIABLE x
    Init == x = 1 \\/ x = 2 
    Next == x' = 2
    ====`;
    initExpected = [{x:1}, {x:2}];    
    nextExpected = [{"x":1, "x'":2}, {"x":2, "x'":2}]
    testStateGen("simple-spec2", spec2, initExpected, nextExpected);
}

function simple_spec3(){
    let spec3 = `----------------------- MODULE Test ------------------------
    VARIABLE x
    VARIABLE y
    Init == 
        /\\ x = 1 \\/ x = 2 
        /\\ y = 3 \\/ y = 4
    
    Next == x' = 2 /\\ y' = 2
    ====`;
    initExpected = [{x:1,y:3},{x:2,y:3},{x:1,y:4},{x:2,y:4}];
    nextExpected = [
        {"x":1, "y":3, "x'":2, "y'": 2}, 
        {"x":1, "y":4, "x'":2, "y'": 2}, 
        {"x":2, "y":3, "x'":2, "y'": 2}, 
        {"x":2, "y":4, "x'":2, "y'": 2}, 
    ]
    testStateGen("simple-spec3", spec3, initExpected, nextExpected);
}

function simple_spec4(){
    let spec4 = `----------------------- MODULE Test ------------------------
    VARIABLE x
    Init == 
        /\\ x = 1 \\/ x = 2 
    
    Next == x = 1 /\\ x' = 3
    ====`;
    initExpected = [{x:1},{x:2}];
    nextExpected = [
        {"x":1, "x'":3},
    ]
    testStateGen("simple-spec4", spec4, initExpected, nextExpected);
}

function simple_spec5(){
    let spec5 = `----------------------- MODULE Test ------------------------
    VARIABLE x
    VARIABLE y
    Init == 
        /\\ x = 1 \\/ x = 2 
        /\\ y = 3 \\/ y = 4
    
    Next == x = 1 /\\ x' = 2 /\\ y' = 2
    ====`;
    initExpected = [{x:1,y:3},{x:2,y:3},{x:1,y:4},{x:2,y:4}];
    nextExpected = [
        {"x":1, "y":3, "x'":2, "y'": 2}, 
        {"x":1, "y":4, "x'":2, "y'": 2}, 
    ]
    testStateGen("simple-spec5", spec5, initExpected, nextExpected);
}

tests = {
    "simple-spec1": simple_spec1,
    "simple-spec2": simple_spec2,
    "simple-spec3": simple_spec3,
    "simple-spec4": simple_spec4,
    "simple-spec5": simple_spec5,
}

const start = performance.now();

const urlSearchParams = new URLSearchParams(window.location.search);
const params = Object.fromEntries(urlSearchParams.entries());
const arg = params["test"];

// Allow URL arg to choose which test to run.
let testNames;
if(arg==="all" || arg === undefined){
    testNames = Object.keys(tests);
    testNames.sort();
} else{
    testNames = [arg];
}

// Run the specified tests.
for(const name of testNames){
    tests[name]();
}


// Measure test duration.
const duration = (performance.now() - start).toFixed(1);
console.log(`All tests ran in ${duration}ms`);

})();