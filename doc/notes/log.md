## 2023-01-08

May want to have a better way for syncing UI model state with URL query parameters e.g. on every update to the model, re-sync the necessary subset of state we want to store in the URL query path.

## 2024-01-26

May be able to use eval graph as structure for compiling to lower level representation (e.g. C++), but think I may need to also record evaluation order, which matters for how eval nodes process incoming values. For example, conjunctions may need to process children in proper order so that contexts are updated appropriately. For disjunctions, I don't think this holds true, since contexts coming back can be process (and combined) in any order.