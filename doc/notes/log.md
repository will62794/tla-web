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