//
// Test script runs on 'test.html' page.
//

let tree;

function toggleTestDetails(testId){

    // alert("details"+testId);
    let resultsDivId = "test_result_details_" + testId;
    let testResultsDiv = document.getElementById(resultsDivId);
    let isHidden = testResultsDiv.getAttribute("hidden");
    // Hide.
    if(isHidden===null){
        testResultsDiv.setAttribute("hidden", true);
    } else{
        // Unhide.
        testResultsDiv.removeAttribute("hidden");
    }
    console.log(isHidden);

}

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

        // Show the spec text and test name first.
        let testHeader = document.createElement("h2");
        testHeader.innerText = "Test: " + testId + "";
        testHeader.style = "cursor:pointer";
        testHeader.setAttribute("onclick", `toggleTestDetails(\"${testId}\")`);
        testsDiv.appendChild(testHeader);

        let detailedResultsDiv = document.createElement("div");
        detailedResultsDiv.id = "test_result_details_" + testId;

        let specCodeDiv = document.createElement("div");
        specCodeDiv.style = "background-color:rgb(230,230,230);width:70%;margin-bottom:15px;";
        let specCode = document.createElement("code");
        specCode.innerText = specText;
        specCodeDiv.appendChild(specCode);
        detailedResultsDiv.appendChild(specCodeDiv);

        tree = null;
        const newTree = parser.parse(specText + "\n", tree);
        
        // Test correct initial states.
        let initStates = computeInitStates(newTree);
        const passInit = arrEq(initExpected, initStates);

        // Print expected initial states.
        div = document.createElement("div");
        div.innerHTML = "<b>Initial states expected:</b>"
        detailedResultsDiv.appendChild(div);
        for(const state of initExpected){
            let stateDiv = document.createElement("div");
            stateDiv.innerText = JSON.stringify(state);
            detailedResultsDiv.appendChild(stateDiv);
        }

        // Print generated initial states.
        div = document.createElement("div");
        div.innerHTML = "<b>Initial states actual:</b>"
        detailedResultsDiv.appendChild(div);
        for(const state of initStates){
            let stateDiv = document.createElement("div");
            stateDiv.innerText = JSON.stringify(state);
            detailedResultsDiv.appendChild(stateDiv);
        }

        // If given expected next states are null, don't check correctness of next states. 
        let passNext;
        if(nextExpected!==null){
            // Test correct next states.
            let nextStates = computeNextStates(newTree, initStates).map(c => c["state"]);
            passNext = arrEq(nextExpected, nextStates);

            // Print expected next states.
            div = document.createElement("div");
            div.innerHTML = "<b>Next states expected:</b>"
            detailedResultsDiv.appendChild(div);
            for(const state of nextExpected){
                let stateDiv = document.createElement("div");
                stateDiv.innerText = JSON.stringify(state);
                detailedResultsDiv.appendChild(stateDiv);
            }

            // Print next states.
            div = document.createElement("div");
            div.innerHTML = "<b>Next states actual:</b>"
            detailedResultsDiv.appendChild(div);
            for(const state of nextStates){
                let stateDiv = document.createElement("div");
                stateDiv.innerText = JSON.stringify(state);
                detailedResultsDiv.appendChild(stateDiv);
            }
        }

        // Append the detailed results and make it hidden by default.
        // TODO: Re-enable hiding test results by default once it can work
        // separately for single tests and all tests.
        // detailedResultsDiv.setAttribute("hidden", true);
        testsDiv.appendChild(detailedResultsDiv);

        // Show the outcome of the test (PASS/FAIL).
        let statusText = "Init: " + (passInit ? "PASS &#10003" : "FAIL &#10007");
        let statusColor = passInit ? "green" : "red";
        div = document.createElement("div");
        div.innerHTML = statusText;
        div.style = "font-weight: bold; color:" + statusColor;
        testsDiv.appendChild(div);

        if(nextExpected!==null){
            statusText = "Next: " + (passNext ? "PASS &#10003" : "FAIL &#10007");
            statusColor = passNext ? "green" : "red";
            div = document.createElement("div");
            div.innerHTML = statusText;
            div.style = "font-weight: bold; color:" + statusColor;
            testsDiv.appendChild(div);
        }
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
    nextExpected = [{"x":1, "x'":2}]
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

function simple_lockserver_nodefs(){
    let speclockserver = `---- MODULE lockserver_nodefs ----
    EXTENDS TLC, Naturals
    
    VARIABLE semaphore
    VARIABLE clientlocks
    
    Init == 
        /\\ semaphore = [i \\in {0,1} |-> TRUE]
        /\\ clientlocks = [i \\in {88,99} |-> {}]
    
    Next == 
        \\/ \\E c \\in {88,99}, s \\in {0,1} : 
            /\\ semaphore[s] = TRUE
            /\\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \\cup {s}]
            /\\ semaphore' = [semaphore EXCEPT ![s] = FALSE]
        \\/ \\E c \\in {88,99}, s \\in {0,1} : 
            /\\ s \\in clientlocks[c]
            /\\ clientlocks' = [clientlocks EXCEPT ![c] = clientlocks[c] \\ {s}]
            /\\ semaphore' = [semaphore EXCEPT ![s] = TRUE]
    
    ====`;
    console.log(speclockserver);
    initExpected = [
        {semaphore:{0:true,1:true}, clientlocks:{88:[], 99:[]}}
    ];
    nextExpected = [
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:false,1:true}, "clientlocks'": {88:[0], 99:[]}},
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:false,1:true}, "clientlocks'": {88:[], 99:[0]}},
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:true,1:false}, "clientlocks'": {88:[], 99:[1]}},
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:true,1:false}, "clientlocks'": {88:[1], 99:[]}},
    ]
    testStateGen("simple_lockserver_nodefs", speclockserver, initExpected, nextExpected);
}

// (*
//     /\\ i \\in voteQuorum
//     /\\ currentTerm' = [s \\in {44,55,66} |-> IF s \\in voteQuorum THEN currentTerm[i] + 1 ELSE currentTerm[s]]
//     /\\ state' = [s \\in {44,55,66} |->
//                 IF s = i THEN "Primary"
//                 ELSE IF s \\in voteQuorum THEN "Secondary"
//                 ELSE state[s]]
//     /\\ configTerm' = [configTerm EXCEPT ![i] = currentTerm[i] + 1]
//     /\\ UNCHANGED <<config, configVersion>>  *)


// /\\ i \\in config[i]
// \\E i \\in {44,55,66} : 
        
let specmldr1 = `---- MODULE mldr ----
EXTENDS TLC, Naturals

VARIABLE currentTerm
VARIABLE state
VARIABLE config

Init == 
    /\\ currentTerm = [i \\in {44,55} |-> 0]
    /\\ state       = [i \\in {44,55} |-> "Secondary"]
    /\\ \\E initConfig \\in SUBSET {44,55} : initConfig # {} /\\ config = [i \\in {44,55} |-> initConfig]

Next == 
    \\/ \\E i \\in {44,55} : 
        \\E voteQuorum \\in {S \\in SUBSET {44,55} : Cardinality(S) * 2 > Cardinality({44,55})} : 
            /\\ i \\in config[i]
            /\\ currentTerm' = [s \\in {44,55} |-> IF s \\in voteQuorum THEN currentTerm[i] + 1 ELSE currentTerm[s]]
            /\\ state' = [s \\in {44,55} |-> IF s = i THEN "Primary" ELSE IF s \\in voteQuorum THEN "Secondary" ELSE state[s]]
            /\\ config' = [s \\in {44,55} |-> {}]

====`;

let mldrInitExpected = [
    {   "currentTerm":{"44":0,"55":0},
        "state":{"44":"Secondary","55":"Secondary"},
        "config":{"44":[44],"55":[44]}
    },
    {   "currentTerm":{"44":0,"55":0},
        "state":{"44":"Secondary","55":"Secondary"},
        "config":{"44":[44,55],"55":[44,55]}
    },
    {   "currentTerm":{"44":0,"55":0},
        "state":{"44":"Secondary","55":"Secondary"},
        "config":{"44":[55],"55":[55]}
    },
];

// /\\ \\A v \\in voteQuorum : CanVoteForConfig(v, i, currentTerm[i] + 1)
function mldr_init(){
    // TODO: Will again have to contend with set vs. list ordering issues eventually.
    testStateGen("mldr_init", specmldr1, mldrInitExpected, null);
}

function mldr_next(){
    nextExpected = [
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:false,1:true}, "clientlocks'": {88:[0], 99:[]}},
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:false,1:true}, "clientlocks'": {88:[], 99:[0]}},
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:true,1:false}, "clientlocks'": {88:[], 99:[1]}},
        {semaphore: {0:true,1:true}, clientlocks: {88:[], 99:[]}, "semaphore'": {0:true,1:false}, "clientlocks'": {88:[1], 99:[]}},
    ]
    testStateGen("mldr_next", specmldr1, mldrInitExpected, nextExpected);
}

tests = {
    "simple-spec1": simple_spec1,
    "simple-spec2": simple_spec2,
    "simple-spec3": simple_spec3,
    "simple-spec4": simple_spec4,
    "simple-spec5": simple_spec5,
    "simple_lockserver_nodefs": simple_lockserver_nodefs,
    "mldr_init": mldr_init,
    "mldr_next": mldr_next
}

const start = performance.now();

const urlSearchParams = new URLSearchParams(window.location.search);
const params = Object.fromEntries(urlSearchParams.entries());
const arg = params["test"];

// Allow URL arg to choose which test to run.
let testNames;
if(arg==="all" || arg === undefined){
    testNames = Object.keys(tests);
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
let durationDiv = document.getElementById("test-duration");
durationDiv.style="margin-top:25px;";
durationDiv.innerText = `All ${testNames.length} tests ran in ${duration}ms`;

})();