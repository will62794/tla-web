# TLA+ Web Explorer

This is an interactive, web-based environment for exploring and sharing TLA+ specifications. The motivation is to have a better way to quickly interact with a TLA+ spec and easily share results. For example, having a way to share counterexample traces in a convenient, portable, and repeatable manner. 

A live version of the tool is currently hosted [here](https://will62794.github.io/tla-web/#!/home), and below are some example specs to try out:

- [Lock server](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2Flockserver.tla&constants%5BServer%5D=%7B%22s1%22%2C%20%22s2%22%7D&constants%5BClient%5D=%7B%22c1%22%2C%20%22c2%22%7D)
- [Cabbage Goat Wolf Puzzle](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FCabbageGoatWolf.tla) (animated)
- [Two phase commit](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FTwoPhase_anim.tla&constants%5BRM%5D=%7Brm1%2Crm2%7D) (animated)
- [Paxos](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FPaxos.tla&constants%5BServer%5D=%7B%22s1%22%2C%22s2%22%2C%20%22s3%22%7D&constants%5BSecondary%5D=%22Secondary%22&constants%5BPrimary%5D=%22Primary%22&constants%5BNil%5D=%22Nil%22&constants%5BInitTerm%5D=0&constants%5BAcceptor%5D=%7Ba1%2Ca2%2Ca3%7D&constants%5BQuorum%5D=%7B%7Ba1%2Ca2%7D%2C%7Ba2%2Ca3%7D%2C%7Ba1%2Ca3%7D%2C%7Ba1%2Ca2%2Ca3%7D%7D&constants%5BProposer%5D=%7Bp1%2Cp2%7D&constants%5BValue%5D=%7Bv1%2Cv2%7D&constants%5BBallot%5D=%7B0%2C1%2C2%2C3%7D&constants%5BNone%5D=None)
- [Raft](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FAbstractRaft_anim.tla&constants%5BServer%5D=%7Bs1%2Cs2%2C%20s3%7D&constants%5BSecondary%5D="Secondary"&constants%5BPrimary%5D="Primary"&constants%5BNil%5D="Nil"&constants%5BInitTerm%5D=0) (animated)
- [EWD998](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FEWD998.tla&constants%5BN%5D=3) (animated)
- [Snapshot Isolation](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fwill62794%2Fsnapshot-isolation-spec%2Frefs%2Fheads%2Fmaster%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=%22Empty%22) 

You can also explore some interesting (and infamous) protocol traces:

- (Raft) [Log entry is written and later rolled back](https://will62794.github.io/tla-web/#!/home?specpath=.%2Fspecs%2FAbstractRaft_anim.tla&constants%5BServer%5D=%7Bs1%2Cs2%2Cs3%7D&constants%5BSecondary%5D=%22Secondary%22&constants%5BPrimary%5D=%22Primary%22&constants%5BNil%5D=%22Nil%22&constants%5BInitTerm%5D=0&trace=318c702a%2C0785f33f_61cceca3%2Cbbf1576c_7afb3e6d%2C79ad3285_7afb3e6d%2C708acdc2_d78334f6%2C2cd8de84_0b61fc25%2Cfbeeee44_b23ce684%2Cac5d32a8_52c587a6%2Cc1e2949e_52c587a6%2Cd8547bce_738ebf5a%2C7735c8df_4fff85de) 
- (Snapshot Isolation) [Read-only anomaly under snapshot isolation](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fwill62794%2Fsnapshot-isolation-spec%2Frefs%2Fheads%2Fmaster%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=%22Empty%22&trace=4d9d875e%2C27dfd06a_6bf3d95d%2C639eed1f_769f9e6e%2C4cb5a71b_6d983cb2%2C4708fef8_b438f7fa%2C429a81d3_453b662d%2Ce9311886_b99ec46e%2C7478057a_07032a58%2C2ea8cbe7_30c5c2c6%2C6a3128ec_74240193%2Cd2bef298_3e4a1f73%2C071ae0d9_485f1900) 
- (Snapshot Isolation) [Write skew anomaly under snapshot isolation](https://will62794.github.io/tla-web/#!/home?specpath=https%3A%2F%2Fraw.githubusercontent.com%2Fwill62794%2Fsnapshot-isolation-spec%2Frefs%2Fheads%2Fmaster%2FSnapshotIsolation.tla&constants%5BtxnIds%5D=%7Bt0%2Ct1%2Ct2%7D&constants%5Bkeys%5D=%7Bk1%2Ck2%7D&constants%5Bvalues%5D=%7Bv1%2Cv2%7D&constants%5BEmpty%5D=%22Empty%22&trace=4d9d875e%2Cb0868cc6_cfdcdcd4%2C2f4fe314_6d983cb2%2C351c185a_70b477c1%2C9af072f2_74240193%2C0ad7710e_0142a5e0%2C39e3312d_04a99af6%2Cc5dbe6f2_b99ec46e%2C0005740a_38df124a) 

The current version of the tool utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) for parsing TLA+ specs and implements a [TLA+ interpreter/executor](https://github.com/will62794/tla-web/blob/89d763c6001fa91dfc55780fedd47a9fbbf4e934/js/eval.js#L726-L778) on top of this in Javascript. This allows the tool to interpret specs natively in the browser, without relying on an external language server. The Javascript interpreter is likely much slower than TLC, but efficient model checking isn't currently a goal of the tool. 

<!-- Note also that you can basically use the existing web interface as a simple TLA+ expression evaluator, since making changes to definitions in the spec should automatically update the set of generated initial states. -->

<!-- This project Utilizes the [TLA+ tree-sitter grammar](https://github.com/tlaplus-community/tree-sitter-tlaplus) to provide a web based TLA+ interface for exploring and sharing specifications.  -->
<!-- There are still some TLA+ language features that [may not be implemented](https://github.com/will62794/tla-web/issues), but a reasonable number of specs should be handled correctly. For example, see this [Paxos spec](https://will62794.github.io/tla-web/#!/home?specpath=./specs/Paxos.tla). Additional testing is needed to verify the correctness of this interpreter on more complex specs. -->

<!-- A basic, preliminary test suite can be found [here](https://will62794.github.io/tla-web/test.html). -->

## Usage Notes

The current tool expects that a specification has defined its initial state predicate and next state relation as `Init` and `Next` definitions, respectively. If your specification has these defined under different names, they will not be recognized and no initial state or next state evaluation will occur. In this case, you can still use the tool in REPL mode, though. 

Eventually this will be made configurable, but the current tool looks for these hard-coded definitions. Also, there is incomplete support for user module imports, so specs are largely expected to be written in a single module. The interpreter does, however, support most operators from the [TLA+ standard modules](https://github.com/tlaplus/tlaplus/tree/c25a01393ef7d9b0315f3d3b1581988e7a4a57b2/tlatools/org.lamport.tlatools/src/tla2sany/StandardModules) by default.

You can also see a live demo of the tool and its features in [this presentation](https://www.youtube.com/watch?v=kSSWmxQLvmw), which also gives a very high level overview of the tool architecture and implementation details.

<!-- Note that in addition to copying and pasting in the text of a TLA+ spec or writing it in the browser interface, you can also load a spec file from a given URL by using the following URL path format: -->
<!-- ``` -->
<!-- https://will62794.github.io/tla-web/#!/home?specpath=<tla_spec_url> -->
<!-- ``` -->
<!-- where `tla_spec_url` is a URL pointing to raw TLA+ module file. For example, you can see that [this link](https://will62794.github.io/tla-web/#!/home?specpath=https://gist.githubusercontent.com/will62794/4250c4b6a8e68b0d9e038186739af8cc/raw/3470b5999f896abb478733e8fc07e7ed9e3039da/HourClock.tla) loads a simple spec from a [personal Github gist](https://gist.githubusercontent.com/will62794/4250c4b6a8e68b0d9e038186739af8cc/raw/3470b5999f896abb478733e8fc07e7ed9e3039da/HourClock.tla). -->


<!-- ### REPL Mode -->

<!-- You can also open a specification in REPL mode, which gives you access to a live REPL for dynamically evaluating TLA+ expressions in the context of a specification. See [here](https://will62794.github.io/tla-web/#!/home?specpath=./specs/repl.tla&repl=true) for an example REPL scratchpad. -->

## Testing

Currently, nearly all testing of the tool is done via conformance testing against TLC. That is, for a given specification, we [generate its reachable state graph using TLC](https://github.com/will62794/tla-web/blob/0060a9bedfbf78c9c6ef1eacf701b13f85048f5e/specs/with_state_graphs/gen_state_graphs.sh) and compare this for equivalence against the reachable state graph generated by the Javascript interpreter. You can see the result of all current tests that are run on [this page](https://will62794.github.io/tla-web/test.html), and the underlying test specs [here](https://github.com/will62794/tla-web/tree/0060a9bedfbf78c9c6ef1eacf701b13f85048f5e/specs/with_state_graphs).