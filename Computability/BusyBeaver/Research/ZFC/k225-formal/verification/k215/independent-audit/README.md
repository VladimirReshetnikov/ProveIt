# Independent 215-state endpoint audits

**Both final actual audits pass.** The [Lean review](lean-actual-v1/review.json) checks all 204 current project modules and the exact two typed-client audits. The [Rocq review](rocq-actual-v1/review.json) checks all 237 current modules and the successful recursive `coqchk` run. These independent reviews inspect the recorded kernel runs and current artifacts; they do not claim a second compiler execution.

Both languages prove blank halting iff a finite ZFC refutation, and nonhalting iff its absence, for the exact accepted 215-state machine. The literal binding has 430 actions and 4,751 expanded source leaves. Its 179 internal decision nodes plus 23 primitive leaf kinds give 202 distinct subtrees. The statements have no consistency premise or uninstantiated machine hypothesis. They do not assert unconditional nonhalting, PA internalization, or a separately encoded derivation inside ZFC.

The [Lean raw reports](lean-actual-v1/raw) contain the two independent clients and eight component/client axiom reports. Their only axioms are `propext`, `Classical.choice` and `Quot.sound`; no `sorryAx` or custom axiom occurs. The [Rocq raw reports](rocq-actual-v1/raw) contain two `Closed under the global context` reports for each sparse and dense endpoint. Recursive `coqchk` ran without `-admit` or `-norec`. Its imported global context lists three utility axioms (`inj_pair2`, `proof_irrelevance`, `eq_rect_eq`), which are absent from all four endpoint dependency reports. The [Lean scope](lean-actual-v1/README.md) and [Rocq scope](rocq-actual-v1/README.md) state the precise toolchain and historical capture boundaries.

The final proofs are concise compositions. Lean composes the source equivalences, instantiates one general machine theorem with concrete proofs, and obtains nonhalting by negation. Rocq's sparse endpoint uses two rewrites and its calibrated source theorem; the dense endpoint adds one rewrite. Generated finite certificates remain below these small interfaces. No further proof refactoring is needed to make the endpoint readable.

## Preserved development phases

The [initial source review](actual/endpoint/source-review.md), [initial receipt](actual/endpoint/review.json), and [Rocq command-compiler peer](actual/compiler-peer/review.md) remain unchanged. The former describes the historical 171-module Lean layout. The [monolithic-phase history](history/monolithic-phase/README.md) retains its original checker and pins. The [pre-final README](history/pre-final-actual-readme/README.md) preserves the earlier pending-build status.

The [partition-v2 review](actual/partition-v2/review.json) records the semantics-preserving split of `KSource215` into common data, 32 independent certificate proofs and its original public facade. It is a historical static phase, not a claim that its whole-closure source pins remain current. Subsequent [DomRho8 repair](domrho8-repair-v1/review.json) and [namespace repairs](namespace-repairs-v1/review.json) are recorded separately. The final actual reviews bind the repaired sources. Failed compiler attempts, including the monolithic timeout and failed-source `sorryAx` diagnostics, are preserved and excluded from successful evidence.

The [v2 literal checker](code/literal_bindings_v2.py) and its 17 pinned data inputs remain applicable: the final Lean actual audit independently rechecked every byte against the earlier parsed result. The historical [partition closure census](actual/partition-v2/lean-source-closure.json) should not be substituted for the final current-source receipt.

## Reproduction and review provenance

[EndpointAudit215.lean](EndpointAudit215.lean) expands blank halting and states both equivalences without hypotheses. Its exact bytes were compiled successfully in the final Lean audit. The read-only [Lean evidence auditor](lean-actual-v1/check_actual.py) and [Rocq evidence auditor](rocq-actual-v1/check_actual.py) accept `--build BUILD --repo REPO --output NEW_RESULT.json`; they use Python's standard library, require assertions and a fresh result, and invoke no proof compiler. Full rebuild instructions and archived author evidence are in the adjacent [Lean](../lean/README.md) and [Rocq](../rocq/README.md) lanes.

The portable-runner reviews, including corrected resume-log and toolchain/assumption gates, remain under [portable-lean-v2](portable-lean-v2/review.json), [portable-rocq-v1](portable-rocq-v1/review.json), [portable-rocq-v3](portable-rocq-v3/review.json), and [evidence-helpers-v2](evidence-helpers-v2/review.json). Their source-review scope is distinct from the final actual artifact audits.

Authorship: `drop_contract` authored the independent reviews, literal checker, typed caller and copy-only partition. `opening_encoder` owns Lean adoption, compilation and repairs; `review_upstream_reflection` owns Rocq compilation and repairs. Root separately reviewed and integrated both lanes.
