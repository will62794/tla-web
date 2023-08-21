# TLA+ Web Explorer Prototype

This is a prototype of a web based TLA+ interface for exploring and sharing specifications and traces. The motivation is to have a better way to quickly interact with a TLA+ spec and easily share results. For example, provide a way to share error traces in a convenient, portable, and repeatable manner. A live version of the prototype is currently hosted [here](https://will62794.github.io/tla-web/#!/home). Here are some example specs to try out:

- [Lock server](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2Flockserver.tla&constants%5BServer%5D=%7B%22s1%22%2C%20%22s2%22%7D&constants%5BClient%5D=%7B%22c1%22%2C%20%22c2%22%7D)
- [Two phase commit](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FTwoPhase.tla)
- [Paxos](https://will62794.github.io/tla-web/#!/home?specpath=./specs/Paxos.tla)
- [EWD998](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FEWD998.tla)
- [Raft](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FAbstractRaft.tla&constants%5BServer%5D=%7B"s1"%2C"s2"%2C%20"s3"%7D&constants%5BSecondary%5D="Secondary"&constants%5BPrimary%5D="Primary"&constants%5BNil%5D="Nil"&constants%5BInitTerm%5D=0)

The current version of the tool utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) for parsing TLA+ specs and implements a [TLA+ interpreter/executor](https://github.com/will62794/tla-web/blob/89d763c6001fa91dfc55780fedd47a9fbbf4e934/js/eval.js#L726-L778) on top of this in Javascript. This allows the tool to interpret specs natively in the browser, without relying on an external language server. The Javascript interpreter is likely much less efficient than TLC, but doing efficient model checking isn't currently a goal of the tool. 

<!-- Note also that you can basically use the existing web interface as a simple TLA+ expression evaluator, since making changes to definitions in the spec should automatically update the set of generated initial states. -->

<!-- This project Utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) to provide a web based TLA+ interface for exploring and sharing specifications.  -->
There are still a variety of TLA+ language features that [may not be implemented yet](https://github.com/will62794/tla-web/issues), but a decent number of specs should be handled. For example, this [Paxos example](https://will62794.github.io/tla-web/#!/home?specpath=./specs/Paxos.tla) should be handled, though more thorough testing will be needed to verify the correctness of the interpreter on more complex examples like this.

<!-- A basic, preliminary test suite can be found [here](https://will62794.github.io/tla-web/test.html). -->

## REPL Mode

You can also open a specification in REPL mode, which gives you access to a live REPL for dynamically evaluating TLA+ expressions in the context of a specification. See [here](https://will62794.github.io/tla-web/#!/home?specpath=./specs/repl.tla&repl=true) for an example REPL scratchpad.