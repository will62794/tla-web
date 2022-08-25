# How TLC Computes States

See *Specifying Systems* 14.2.6 for reference.

When TLC evaluates an invariant, it is calculating the invariant's value in the context of a given state. That is, under a particular assignment of values to variables. The result of this evaluation is either TRUE or FALSE. When TLC evaluates the initial predicate or the next state action, it is instead computing a set of states. For the initial predicate, it is the set of all possible initial states. For the next state action, it is the set of possible *successor* states from a given starting state.

Recall that a state is an assignment of values to variables. TLC computes the successors of a given state `s` by assigning to all unprimed variables their values in state `s`, assigning no values to the primed variables, and then evaluating the next-state action. TLC evaluates the next-state action as described in Section 14.2.2 (page 231), except for two differences:
- For disjunctions `A1 \/ ... \/ An`, TLC splits the computation into `n` separate evaluations, one for each subexpression. 
- For any variable `x`, if it evaluates an expression of the form `x' = e` when `x'` has not yet been assigned a value, then the evaluation yields the value `TRUE` and TLC assigns to `x'` the value obtained by evaluating the expression `e`.

An evaluation that completes and obtains the value `TRUE` finds the state determined by the values assigned to the primed variables. An evaluation stops, finding no states, if a conjunct evaluates to `FALSE`.

For computing initial states, TLC follows a similar procedure, but instead of starting from given values of unprimed variables and assigning values to the primed variables, it assignes values to the unprimed variables.