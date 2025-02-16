const fs = require('fs');

const Parser = require('tree-sitter');
const { Query } = Parser
const TLA = require('@tlaplus/tree-sitter-tlaplus');
const eval = require('../../js/eval.js');

var _ = require('lodash');

// Parse spec.
const parser = new Parser();
parser.setLanguage(TLA);

const sourceCode = `
---- MODULE Test ----
VARIABLE x
Init == x = 0
Next == x' = 2
====`;

const tree = parser.parse(sourceCode);

const callExpression = tree.rootNode.toString();
console.log(callExpression)

const query = new Query(TLA, '(def_eq) @capture')
console.log(query.captures(tree.rootNode))

// Set up interpreter.
const interp = new eval.TlaInterpreter();
// initStates = interp.computeInitStates(model.specTreeObjs, model.specConstVals, includeFullCtx, model.spec);

const spec = new eval.TLASpec(sourceCode, "Test", parser);
spec.parseSync();
console.log(spec);
console.log(spec.spec_obj);

// const initStates = interp.computeInitStates(spec.specTreeObjs, spec.specConstVals, true, spec);
// console.log(initStates);