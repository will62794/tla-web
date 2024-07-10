# TLA+ Module Semantics

A given TLA+ module `M` can import other modules via two basic mechanisms:

- `EXTENDS N`
- `INSTANCE N`

which have somewhat different semantics from each other.

## `EXTENDS`

The first, `EXTENDS`, is straightforward, in that it dumps all definitions, declarations (e.g. `VARIABLE` and `CONSTANT` declarations) from `N` into `M`, as if they were simply copy-pasted in.

## `INSTANCE`

The second, `INSTANCE` is a bit different, and also allows for "substitution". 

If you have a statement like `INSTANCE N`, then this dumps all definitions that appear in `N` into the scope of module `M`, but it does not dump the `VARIABLE` or `CONSTANT` declarations from `N`. But, if you use a definition from `N` from within `M`, it must be able to access any symbol that could be accessed within `N`, which include variable or constants declarations in `N`. So, you have to ensure that those same symbols are accessible in `M` as well. 

If symbols with the same nameas those in `N` already appear in `M`, then this is already handled. If not, though, you have to provide explicit substitutions for the symbols that appear in `N` but not in `M`. For example, if `N` declares `VARIABLE y`, but there is no `VARIABLE y` declaration in `M`, then you must provide a substitution for `y` in the `INSTANCE N` statement. For example, if `M` has declared `VARIABLE x`, then you could write 
```tla
INSTANCE N WITH y <- x
```

### Namespaced Instantiation

`INSTANCE` statements can also come in "namespaced" form, where you write something like
```tla
Foo == INSTANCE N WITH ...
```
and then all the definitions from `N` are then dumped into the current module but prefixed with `Foo!`. Again, the same issue arises as above, though, where you ned to ensure that substitutions are provided for any symbols that are not already declared in the current module.

Note also that you can think of `INSTANCE` statements as always providing `WITH` substitutions for all symbols, but if you just write `INSTANCE N`, then this is implicitly treated as identity substitutions for all symbols e.g.
```tla
INSTANCE N WITH x <- x, y <- y, ...
```