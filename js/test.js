//
// Test script runs on 'test.html' page.
//

let testsDiv = document.getElementById("tests");
let p = document.createElement("div");
p.innerHTML = "test #1";
testsDiv.appendChild(p);

let spec1 = `----------------------- MODULE Test ------------------------
EXTENDS Naturals
VARIABLE x
Init == x = 1 
Next == x' = 2
=============================================================================`;