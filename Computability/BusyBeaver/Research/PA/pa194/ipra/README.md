# PA194 bounded halting and conditional PA consistency endpoint

This directory binds the primary PA194 transition table to an arithmetical
halting sentence. It does **not** prove either machine-specific direction of
`iPRA ⊢ Con(PA) ↔ ¬Halt(PA194)`; both reductions remain explicit hypotheses
in the endpoint. The packet's claimed PA equivalence is not an end-to-end Lean
proof or an iPRA proof.

`generate.py` reads the placed packet file
`../../docs/pa194_conpa_2026-11-13/construction/tables/pa194.tm` and checks its
SHA-256 against the original archive member:
`4bfea62b17aad7d8c8c5e682fe8942e0a86b93e4351f8e675e32705bdaae007f`.
The generator validates 388 transitions for all bits and working labels 0–193,
start 0, terminal 194, and graph reachability of all working labels. Parsing,
hash verification, and graph reachability are Python checks, not Lean
theorems. The two temporary Lean table representations come from the same
parsed data; Lean checks that all 388 entries agree.

`PA194Bounded.lean`, adapted from the PA195 bridge, defines a numeric tape
simulation, proves its bounded halting test primitive recursive, and binds it
to the generated literal zipper machine on blank input over standard natural
numbers. A function code is obtained using classical choice, not supplied as
an explicit serialized numeral. `PA194StandardSemantics.lean` identifies the
halting and PA consistency sentences in the standard model. These are not
proofs inside iPRA.

`PA194Endpoint.lean` constructs the desired iPRA equivalence from two explicit
machine-specific reductions. `PA194ForwardGG.lean` transfers one such
reduction from classical PRA, where it remains a hypothesis.
`PA194RefutationBridge.lean` binds the PA refutation formula to Foundation's
PA proof-code predicate in models whose arithmetic reduct satisfies IΣ₁;
this semantic assumption is stronger than the candidate PRA assumptions.
None of these results proves the missing machine-specific reductions.

`PA194PRAAssembly.lean` also reuses the completed machine-independent PA
proof-code witness certificate. It derives the reverse iPRA implication
from a hypothesized classical PRA machine reduction and assembles the
equivalence from both classical PRA reductions; neither reduction is proved.

To reproduce the checks, supply matching prebuilt Lean 4.32 project and
Foundation object directories, for example:

```sh
TMPDIR=/dev/shm \
IPRA_LEAN_OVERLAY=/tmp/current14-standard-fresh-build-20261104/lib \
IPRA_FOUNDATION_OVERLAY=/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
bash Computability/BusyBeaver/Research/PA/pa194/ipra/check.sh
```

The script regenerates the tables and recompiles the local modules in a
private temporary directory. It pins a few direct sources but assumes that
the supplied transitive object caches match their sources; it is not a clean
rebuild of those dependencies. It prints axiom dependencies and rejects
`sorryAx` in the checked declarations.

To rebuild the shared PA witness certificate and check the additional
assembly, use the same environment variables with `check-assembly.sh` in
place of `check.sh`. The same dependency-overlay limitations apply.
