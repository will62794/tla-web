## 2023-01-08

May want to have a better way for syncing UI model state with URL query parameters e.g. on every update to the model, re-sync the necessary subset of state we want to store in the URL query path.

## 2024-01-26

May be able to use eval graph as structure for compiling to lower level representation (e.g. C++), but think I may need to also record evaluation order, which matters for how eval nodes process incoming values. For example, conjunctions may need to process children in proper order so that contexts are updated appropriately. For disjunctions, I don't think this holds true, since contexts coming back can be process (and combined) in any order.

## 2024-07-10

[Github search](https://github.com/search?q=%3D%3D+INSTANCE+language%3ATLA&type=code&ref=advsearch&p=2) of uses of `INSTANCE` across TLA+ code. Parameterized insantiation seems quite rare. [This search](https://github.com/search?q=%22%29+%3D%3D+INSTANCE%22+language%3ATLA&type=code&ref=advsearch) is somewhat more accurate.

Note that for `INSTANCE` module imports, it is the case that only `VARIABLE` and `CONSTANT` declarations can be valid targets for substitution. As reported in one the TLC error messages:

```
Identifier 'ExprM3' is not a legal target of a substitution. 
A legal target must be a declared CONSTANT or VARIABLE in the module being instantiated. 
(Also, check for warnings about multiple declarations of this same identifier.)
```
for a spec that looks like
```tla
---- MODULE simple_extends_instance ----
EXTENDS Sequences, Naturals

INSTANCE simple_extends_M3 WITH ExprM3 <- 43

VARIABLES x

Init == 
    \/ x = ExprM3 + 3

Next == x' = x

====
```
where `simple_extends_M3` contains a definition for `ExprM3`.

## 2024-07-12

TODO: Reconsider clone calls throughout in expression evaluation, in cases where copies may not be strictly necessary.

## 2024-12-24

Note that in general there may be more work needed to precisely handle evaluation of expressions with respect to definition context. For example, the JS interpreter seems to handle the following spec currently:

```tla
---- MODULE simple2 ----
EXTENDS Naturals

VARIABLE x

A == B + 2

B == 1

Init == 
    /\ x = [i \in {0,A} |-> {}]

Next == 
    \/ \E b \in {0,A}, c \in {88,99} : x' = [x EXCEPT ![b] = x[b] \cup {c}]

====
```
but is rejected by TLC, because the definition of `B` is not in scope yet when `A` is defined. This could work in theory but TLC/TLA+ seems to define definitions in a way such that their evaluation is tied to the definitions that were in scope at the time they were defined. May need to thread a few changes through the interpreter to make this work in all cases and match TLC. 

This may also help iron out the subtleties related to lazy evaluation, where we want to evaluate defined expressions in different contexts/scopes.