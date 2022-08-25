# How the TLA+ Interpreter Evaluates Expressions

The evaluation of a TLA+ expression may produce either (1) a value or (2) a set of states along with a value. The first case is the simplest to handle, and deals with basic "constant level" expressions of TLA+ e.g. evaluating expressions like
```
2 + 3
{1,2,3} \cup {3,4}
Append(<<1,2>>, 5)
```
TLA+ expressions can also be evaluated in the context of initial state or next state generation, where the aim is not to evaluate an expression as a single value, but rather to generate a set of states satisfying the given TLA+ state (or action) predicate. 

## Initial State Generation

It is simplest to first consider initial state generation, since next state generation is not fundamentally different. Given a set of defined variables and a TLA+ formula, like
```tla
x = 1 \/ x = 2
```
the problem of initial state generation can be viewed as essentially a type of [satisfiability problem](https://en.wikipedia.org/wiki/Boolean_satisfiability_problem). That is, the goal is to generate the set of all possible assignments to state variables that make the given formula true. More generally, we can also view it as a variant of a [constraint satisfaction problem](https://en.wikipedia.org/wiki/Constraint_satisfaction_problem) (CSP), where the variable domains are initially unknown. In practice, only formulas that allow variables to range over finite domains can be handled, so we can assume that all variable domains are finite. 

Standard algorithms for satisfiability like [DPLL](https://en.wikipedia.org/wiki/DPLL_algorithm) typically assume that formulas are given in [CNF](https://en.wikipedia.org/wiki/Conjunctive_normal_form), and that the variable domains are finite and fixed upfront (e.g. boolean domains, in the case of classic SAT). In the case of state generation in TLA+, though, the setting is a bit different, since formulas may be of arbitrary form, and variables may range over finite but unknown domains. Furthermore, TLA+ permits first order logical constructs (e.g. quantifiers), which falls out of the scope of classic SAT algorithms. So, the algorithm for state generation can not be naively reduced to a classic backtracking/search-based satisfiability algorithm. One potential approach would be to simply encode a TLA+ formulas to SMT, and then generate the set of all satisfying assignments. This may eventually be a feasible approach, but requires more work on developing a clean encoding for all constructs of TLA+ ([TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) and [Apalache](https://github.com/informalsystems/apalache) have worked on this).

The intuition behind the algorithm for state generation can be illustrated by focusing on a few simple examples. A key concept of the evaluation algorithm is that of an *evaluation context*, which is the term we use in our interpreter. Essentially, a context represents all of the state relevant to a current, in-progress state generation procedure, for a single branch of the evaluation computation. Most importantly, it sotres the current assignment of values to state variables, which may be partial, or empty (no variables have values assigned yet). The evaluation function can be viewed as taking on the following signature i.e. it takes in a set of contexts and an expression, and returns a new set of contexts.
```
eval(set<Context>, expr) -> set<Context>
```

As an example, consider the task of generating all initial states satisfying the following TLA+ formula:

```
x = 1 \/ x = 2
```
Initially, we begin with a single, empty context, in which no state variables are assigned any values. 

```
eval({}, x = 1 \/ x = 2)
```

If we encounter a disjunction, during evaluation, then this splits our current computation into two new branches. In the above case, we would split the computation, and then be left with one new formula in each branch:

```
eval({}, x = 1 \/ x = 2)
    eval({}, x = 1)
    eval({}, x = 2)
```
Each of these sub-evaluations then both produce new contexts, since they both contains variable assignments

```
eval({}, x = 1 \/ x = 2) -> {{x=1}, {x=2}}
    eval({}, x = 1) -> {x=1}
    eval({}, x = 2) -> {x=2}
```

TODO.

## Implementation Details

The evaluation of an initial state predicate/expression can be viewed as returning both a boolean value (`TRUE/FALSE`) as well as a set of possible states, i.e. assignments to variables that satisfy the initial state predicate. Whenever we evaluate a conjunction list 
```tla
Expr == A1 /\ ... /\ An
```
we want to compute the boolean value of each expression, and the value of `Expr` is then the conjunction of all of these boolean values. Similarly, for generating possible states, we start off with a set of currently generated (possibly partial) states, and for each of these, we go through each conjunction and evaluate it in the context of that partial state assignment, updating any assignments as necessary. For a disjunction 
```tla
Expr == A1 \/ ... \/ An
```
we split the evaluation into `n` branches. The overall boolean value of `Expr` is, similarly, the disjunction of the values of all `Ai` subformulas, but the set of possible states now becomes the union of the possible states generated by each subformula, where each subformula is given the current context to generate states from.

```javascript
expr_context = {
    // The currently computed 
    // value of an expression.
    "val": Val
    // The list of (possibly partial) states so far 
    // generated up to the current context
    // of this expression evaluation.
    "states": [State]
}
```
