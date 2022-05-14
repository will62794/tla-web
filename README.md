# TLA+ Web Explorer Prototype

This is a prototype of a web based TLA+ interface for exploring and sharing specifications and traces. The motivation is to have a better way to quickly interact with a TLA+ spec and easily share results. For example, provide a way to share error traces in a convenient, portable, and repeatable manner. A live version of the prototype is currently hosted [here](https://will62794.github.io/tla-web/). Here are some example specs to try out:

- [Lock server](https://will62794.github.io/tla-web/?specpath=.%2Fspecs%2Flockserver.tla)
- [Two phase commit](https://will62794.github.io/tla-web/?specpath=.%2Fspecs%2FTwoPhase.tla)
- [Paxos](https://will62794.github.io/tla-web/?specpath=.%2Fspecs%2FPaxos.tla#)

The current version utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) for parsing TLA+ specs and implements a [TLA+ interpreter/executor](https://github.com/will62794/tla-web/blob/89d763c6001fa91dfc55780fedd47a9fbbf4e934/js/eval.js#L726-L778) on top of this in Javascript. This allows the tool to interpret specs natively in the browser, without relying on an external language server. The Javascript interpreter is likely much less efficient than TLC, but doing efficient model checking isn't a goal of the tool. Note also that you can basically use the existing web interface as a simple TLA+ expression evaluator, since making changes to definitions in the spec should automatically update the set of generated initial states.

<!-- This project Utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) to provide a web based TLA+ interface for exploring and sharing specifications.  -->
There are still a variety of TLA+ language features that [aren't implemented yet](todo.md), but a fair number of specs should work. For example, this [Paxos example](https://will62794.github.io/tla-web/?specpath=.%2Fspecs%2FPaxos.tla#) should be handled, though I can't confidently guarantee that the interpreter behavior is fully correct on more complex examples like this without more thorough testing.

<!-- A basic, preliminary test suite can be found [here](https://will62794.github.io/tla-web/test.html). -->