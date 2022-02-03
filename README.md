# TLA+ Web UI Prototype

This is a prototype of a web based TLA+ interface for exploring and sharing specifications and traces. The motivation is to have a better way to quickly interact with a TLA+ spec and easily share results. For example, provide a way to share error traces in a convenient, portable, and repeatable manner. 

The current version utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) for parsing TLA+ specs and implements a [TLA+ interpreter/executor](https://github.com/will62794/tla-web/blob/89d763c6001fa91dfc55780fedd47a9fbbf4e934/js/eval.js#L726-L778) on top of this in Javascript. This allows the tool to interpret specs natively in the browser, without relying on any kind of external language server. The Javascript interpreter most likely isn't as efficient as TLC, but doing highly efficient model checking isn't a goal of the tool. There are still some TLA+ language features that aren't implemented yet, but a fair number of basic specs should work. For example, this [Paxos example](https://will62794.github.io/tla-web/?specpath=.%2Fspecs%2FPaxos.tla#) should be handled, though I can't confidently guarantee that the interpreter behavior is fully correct on more complex examples like this without more thorough testing.

<!-- This project Utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) to provide a web based TLA+ interface for exploring and sharing specifications.  -->
A live version of the in-progress tool is currently hosted [here](https://will62794.github.io/tla-web/). 

<!-- A basic, preliminary test suite can be found [here](https://will62794.github.io/tla-web/test.html). -->