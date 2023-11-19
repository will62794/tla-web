# TLA+ Web Explorer

This is a web-based interface for exploring and sharing TLA+ specifications. The motivation is to have a better way to quickly interact with a TLA+ spec and easily share results. For example, having a way to share counterexample traces in a convenient, portable, and repeatable manner. 

A live version of the tool is currently hosted [here](https://will62794.github.io/tla-web/#!/home), and here are some example specs to try out:

- [Lock server](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2Flockserver.tla&constants%5BServer%5D=%7B%22s1%22%2C%20%22s2%22%7D&constants%5BClient%5D=%7B%22c1%22%2C%20%22c2%22%7D)
- [Two phase commit](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FTwoPhase.tla)
- [Paxos](https://will62794.github.io/tla-web/#!/home?specpath=./specs/Paxos.tla)
- [Raft](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FAbstractRaft.tla&constants%5BServer%5D=%7B"s1"%2C"s2"%2C%20"s3"%7D&constants%5BSecondary%5D="Secondary"&constants%5BPrimary%5D="Primary"&constants%5BNil%5D="Nil"&constants%5BInitTerm%5D=0)
- [EWD998](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FEWD998.tla)

The current version of the tool utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) for parsing TLA+ specs and implements a [TLA+ interpreter/executor](https://github.com/will62794/tla-web/blob/89d763c6001fa91dfc55780fedd47a9fbbf4e934/js/eval.js#L726-L778) on top of this in Javascript. This allows the tool to interpret specs natively in the browser, without relying on an external language server. The Javascript interpreter is likely much less efficient than TLC, but doing efficient model checking isn't currently a goal of the tool. 

<!-- Note also that you can basically use the existing web interface as a simple TLA+ expression evaluator, since making changes to definitions in the spec should automatically update the set of generated initial states. -->

<!-- This project Utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) to provide a web based TLA+ interface for exploring and sharing specifications.  -->
There are still some TLA+ language features that [may not be implemented](https://github.com/will62794/tla-web/issues), but a reasonable number of specs should be handled correctly. For example, see this [Paxos spec](https://will62794.github.io/tla-web/#!/home?specpath=./specs/Paxos.tla). Additional testing is needed, though, to verify the correctness of this interpreter on more complex specs.

<!-- A basic, preliminary test suite can be found [here](https://will62794.github.io/tla-web/test.html). -->

## Usage Notes

The current tool expects that a specification has defined its initial state predicate and next state relation as `Init` and `Next` definitions, respectively. If your specification has these defined under different names, an error will be reported and spec evaluation will fail. Eventually this will be made configurable, but the current tool looks for these hard-coded definitions. Also, there is currently no support for user module imports, so specs are expected to be written in a single module. The interpreter does, however, by default support most operators from the [TLA+ standard modules](https://github.com/tlaplus/tlaplus/tree/c25a01393ef7d9b0315f3d3b1581988e7a4a57b2/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules).

Note that in addition to copying and pasting in the text of a TLA+ spec or writing it in the browser interface, you can also load a spec file from a given URL by using the following URL path format:
```
https://will62794.github.io/tla-web/#!/home?specpath=<tla_spec_url>
```
where `tla_spec_url` is a URL pointing to raw TLA+ module file. For example, you can see that [this link](https://will62794.github.io/tla-web/#!/home?specpath=https://gist.githubusercontent.com/will62794/4250c4b6a8e68b0d9e038186739af8cc/raw/3470b5999f896abb478733e8fc07e7ed9e3039da/HourClock.tla) loads a simple spec from a [personal Github gist](https://gist.githubusercontent.com/will62794/4250c4b6a8e68b0d9e038186739af8cc/raw/3470b5999f896abb478733e8fc07e7ed9e3039da/HourClock.tla).


### REPL Mode

You can also open a specification in REPL mode, which gives you access to a live REPL for dynamically evaluating TLA+ expressions in the context of a specification. See [here](https://will62794.github.io/tla-web/#!/home?specpath=./specs/repl.tla&repl=true) for an example REPL scratchpad.