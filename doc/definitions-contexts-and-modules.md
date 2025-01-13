# Definitions, Contexts, and Module Instantiation

In general, within any root module `M`, it may contain some set of declarations (`VARIABLE` and/or `CONSTANT`) and definitions (e.g. `Def == 5`). 
A definition is ultimately a mapping from some name (e.g. `Def`) to some given expression (e.g. `5`). Within the expression of such a definition, though, it may refer to other definitions e.g.

```tla
---- MODULE M ----
Val == 2
Def == Val + 5
====
```
In general, we could consider "expanding" all such expressions that appear in a module so that no expressions refer to other definitions, but rather, only to either *variables, primed variables, model values, and built-in TLA+ operators and constants*. 

Although we could in theory apply this expansion to every defined expression, we may not want to in practice, since we may, for example, want to only do such a process lazily, or on the fly as we evaluate expressions. So, we need a slightly more nuanced model of how we view definitions and their meaning.

At any point within a module `M`, we can consider there to be a current **context** of variable declarations, constant declarations, and definitions that exist i.e. have been defined or imported previously. So, when a definition is created, we can consider it as being created within the "scope" of the current state of this context, $C_{curr}$. That is, any elements of this definition's expression can make reference to definitions or declarations within $C_{curr}$. This means that, in this model, a definition fundamentally consists of both a name to expression mapping, but must also be coupled with a "scope", which is a context of definitions and declarations that existed when it was defined.

## Module Instantiation

If we don't consider module `EXTENDS` or `INSTANCE` operations, then the above details are sufficient to cover the semantics of definitions. Having the ability to import other modules, though, complicates this a bit.

The simplest form of module instantiation is by use of the `EXTENDS M` statement, where `M` is some other module we assume we can look up or find access to. This form of module import simply adds all definitions and declarations from `M` to the current context of the module containing this statement. Note that this assumes `M` has already been parsed and processed to the point where we know its full set of definitions and declarations. In order to do this, we may need to recursively look up imported modules until we get to a "leaf" module that has no imported definitions, and so can be parsed and processed indepenently.

The `INSTANCE M` statement behaves similarly to `EXTENDS M`, with some subtle differences. In general, it may come in two forms, either *namespaced* (the first form below) or not (the second form below):
```tla
MInst == INSTANCE M
INSTANCE M
```
The first form also imports all definitions and declarations from `M` into the context of the current module, but it prefixes all such names with `MInst!`. The second form does the same, except without the name prefixing.

### Substitutions

There is an additional aspect of instantation unique to the `INSTANCE` statement that is not present with `EXTENDS` statement. Specifically, for any `INSTANCE M` statement (namespaced or not), all declarations (variables and constants) that appear in `M` must be assigned with some meaningful expressions via *substitutions*. So, in fact, any instance statement really can be viewed as the more general form :
```
INSTANCE M WITH d1 <- e1, d2 <- e2, ...
```
where `d1`, `d2`, etc. are the names of declarations in `M`, and `e1`, `e2`, etc. are the expressions that assign some meaning to these declarations. By convention, if an `INSTANCE` statement does not specify any substitutions, then it is assumed to implicitly assign an "identity" substitution to all such declarations e.g.
```
INSTANCE M
```
is interpreted equivalently to
```
INSTANCE M WITH d1 <- d1, d2 <- d2, ...
```
assuming `d1`, `d2`, etc. are the names of all declarations in `M` (and also exist within the context of the current module). A substitution of the form `d1 <- e1` means that, for any definition that was imported from `M` via this `INSTANCE` statement, a reference to `d1` in this definition will now refer to `e1`. 

So, when we consider substitutions, this means that definitions also have an additional bit of context information, which tells you what substitutions to perform i.e. a definition can be viewed as containing
- **definition**: the definition itself, which is a mapping from a name to expression.
- **scope**: the set of declarations and definitions that existed when this definition was created/instantiated.
- **substitutions**: the set of substitutions that are in effect for this definition's expression.

Note, importantly, that substitutions have subtle scoping semantics. For example, the evaluation of `e1`, the expression that was substitued for `d1`, really exists within the context of the current module, not in the context of some point in `M`. So, when specifically evaluating `e1` its context should be that the context that was current at the time of `INSTANCE` statement in the root module.









