# Batch 219: eight proof-simplification packets

Reviewed placement: [`56b37bde8b064d852154ad8478d58ec9ab5375d6`](https://github.com/VladimirReshetnikov/ProveIt/commit/56b37bde8b064d852154ad8478d58ec9ab5375d6). The packets use the older `cbf94cb552a3b49509e0eee80e7455d4eb5974c6` source baseline. This review combines two independent source reviews against phase21 and the selected phase22 sources. It recommends **Lean work only**; the Rocq components remain mathematical references or already adopted history.

The strongest follow-ups are a deliberate combination of the generic semantic import cut with native Replacement, and one Lean mixed-coverage pilot based on `framed-control`. The four frame libraries overlap substantially. Their projected savings must not be added.

## Eight-packet decision table

| Packet | Useful contribution | Overlap or limitation | Lean action |
|---|---|---|---|
| [checked-local-contracts](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/checked-local-contracts/README.md) | Universal guarded frame/source contracts and concrete engine/Home instances for 35 templates. | The template family is inherited round13 work, repeated in two other packets and improved by `framed-control`. Its exact macro transport repeats a mechanism already used by Lean. | Use its semantic boundary as reference; integrate one frame implementation, using `framed-control`. |
| [contextual-contracts](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/contextual-contracts/README.md) | Pointwise structured-run transport and a concrete increment-node 188/190 commutation; another 35-template family. | Some concrete-looking runtime theorems still take engine/Home premises. The commutation does not supply the full source-to-CFG bridge or replace the normalized source certificate. | Keep the commutation argument as a separate mathematical reference; use the stronger frame basis below. |
| [framed-control](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/framed-control/README.md) | Return through state 1 **or 2**, with a verified read-only return word: 20 templates, 239 symbolic operations, 1,423 caller records, concrete engine premises and role-route witnesses. | Caller-list validity is not total source-outcome coverage. The component adds 31 Lean files; no net endpoint reduction is established. | Preferred basis for one Lean residual/coverage integration pilot. |
| [proof-sharing](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/proof-sharing/README.md) | A bounded scheduler theorem and adapter to current `EnumPerm.build_c222`. | Its 35-template runtime repeats the other packets. Qualitative cofinal scheduling is prior work; the triangular bound is optional and is not a binary-machine time bound. | Try a narrow shared qualitative scheduler across the four current enumerators; count its adapters and remove displaced proofs before claiming savings. |
| [checked-interfaces](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/checked-interfaces/README.md) | Five normalization-first `ConstructibleAbs` proofs; careful checked-lookup boundary and negative helper results. | The normalization is already adopted, byte for byte, by attributed cherry-pick `d0cb4828f0` from Claude's `5a26d6`. The optional tree backend is larger and slower than its own list baseline. | Preserve the adopted normalization and its provenance. No additional backend work is selected. |
| [consolidation-plan](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/consolidation-plan/README.md) | Native Replacement from existing formula-indexed quotient Collection, including the necessary import split; optional reachable-suffix termination transport. | Native Replacement implements earlier guarded-image ideas. Its import split overlaps `proof-spine`. Termination transport adds 188 production lines for one shortened client. | Prioritize native Replacement with a deliberately merged semantic Core split. Defer the termination library until real reuse pays for it. |
| [source-identity](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/source-identity/README.md) | Exact identification of the decoder's second source presentation with the actual program; explicit direct-walk proof obligations. | AX inference overlays predate phase20/21 sharing and name a retired producer. The broad subtype helper increases source. Claude already adopted `z465` loop reuse upstream in `6e1a532d89`. | Keep the direct-program decoder direction separate. Preserve shared `AXWord`/`AXExpr`; do not apply the stale overlays or start new Rocq work. |
| [proof-spine](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/proof-spine/README.md) | Four generic semantic Core/facade splits and a decrement-prefix fork composed from existing executor soundness. | Both proposals are uncompiled candidates. The cut reduces a selected import closure while increasing total maintained source; finite replay counts are not build timings. | Merge the Core cut with native Replacement carefully. Consider the Lean fork lemma as a separate component before changing coverage checks. |

## Evidence and publication boundary

Both peer reviews are **source-only**: READMEs, complete TeX reports/includes, selected proof sources, mathematical scopes and inert Git bytes were inspected. No supplied program, proof, compiler or TeX build was executed. The two selections retain provenance for **221 + 211 = 432 placed Git blobs**. ZIP intake was not repeated and checksum manifests were not verified. Placement deliberately omitted duplicate repository sources and logs; these directories must not be described as intact original replay archives.

Recorded kernel claims remain attributed claims about their bound component sources. For Lean, `checked-local-contracts` reports a 17-module check; `proof-sharing` reports 14 runtime and 17 scheduler modules; `framed-control` reports a 51-module component with 23 caller batches; `checked-interfaces` reports 25 compiler invocations and identical six-declaration reports; native Replacement reports 109 invocations through the generic endpoint and compatibility clients. These scopes do not establish a fresh literal K215 endpoint build, and omitted raw logs were not reconstructed. `source-identity` and `proof-spine` explicitly label their new proposals uncompiled.

Current phase22 validation is separate from this source-only packet review.
Semantic v1 was rejected because global `iff_congr` added `propext`. Constructive
v2 restored the exact profiles, then stopped on an inherited unused-section
warning. V3 applies the reviewed cleanup in `KLowerRaw`, `KLowerTag`, `KLowerQHyp`,
`KQ1Model` and `KQ1Basic`: five signatures lose nine unused assumptions, ten calls
are updated, and four unused witness positions keep their types under underscore
binder names. The terminal kernel run and independent actual readback now **PASS**:
226 providers, 56 fresh, 170 exact reuses, plus two endpoint audits, with zero fresh
warnings and exact accepted profiles. Both stopped prefixes remain history.
**Evidence capture and independent capture review also pass.** See the [phase22 checkpoint](README.md);
this does not promote the packets' prospective components to production acceptance.

The already adopted changes remain separately attributed: [upstream ConstructibleAbs normalization](https://github.com/VladimirReshetnikov/ProveIt/commit/5a26d6d80568090140d5e4a775837a7769f30ed1), adopted locally as attributed cherry-pick `d0cb4828f0`, and [upstream `z465` loop reuse](https://github.com/VladimirReshetnikov/ProveIt/commit/6e1a532d892dcc3602555f5206cec180a33f554f). The latter's recorded check covers the 215 slice; it is history, not a request for further Rocq work.

## Runtime overlap and complete coverage

The repeated 35-template libraries describe the same projected **1,387** reduction in expensive local checks. This is not three separate savings. `framed-control` improves that family to the projection

```text
20 shared bodies + 2 literal control exceptions
+ 1,900 increments + 2,850 decrement outcomes + 1 halt = 4,773
```

The resulting **1,403** reduction from 6,176 is an alternative projection, not an addition to 1,387. Likewise, 239 symbolic operations and 22.72% fewer projected checks are neither concrete TM steps nor measured source/build savings. The decrement-fork packet's 36.26%/39.12% figures measure still another quantity—abstract decrement replay calls—and cannot be added to these counts.

The 1,423 supplied caller records are distinct, with checked contracts and maintained role-route witnesses **for list members**. Acceptance still needs a total classifier: every actual source leaf/outcome must select a compatible caller or a literal fallback. Keep all **4,751 leaves / 6,176 guarded outcomes**, including both decrement branches, two literal control exceptions, register permutation/spares, overflow/gap arithmetic and the actual halt row. Compose exact consumed-prefix ports with residual contracts and the semantic simulator. Semantic reachability does not imply acceptance by the old fixed-fuel Boolean checker.

The direct-program decoder proposal is compatible with this route, but its structural terminal check only distinguishes a primitive edge from an internal node and binds a physical action. It does not prove the primitive opcode's semantics. Its missing direct-walk induction must retain zero extension, consumed depth, the entire source prefix and the exact port; residual and return contracts remain necessary.

A separate interaction concerns [exact macro footprint transfer](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/checked-local-contracts/proof/rocq/Footprint215.v) and [188/190 commutation](https://github.com/VladimirReshetnikov/ProveIt/blob/56b37bde8b064d852154ad8478d58ec9ab5375d6/Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification/proposals/contextual-contracts/rocq/source/src/Refactor/TwoNodeCommutation.v). Nodes 188 and 190 belong to the 89-node exact-agreement footprint. Swapping them invalidates that exact node agreement. Compose transfer to the original program first and pointwise transport to the commuted program second, or supply explicit extensional adapters; do not claim exact final-function equality after commutation. This is a mathematical compatibility note only.

## Native Replacement plus the semantic spine

The guarded-image argument uses the actual Collection support clause: support witnesses need not lie in the requested domain, so the input-domain guard is essential. Partial functionality suffices; totality and choice are unnecessary for the generic image lemma. Its formula adapter swaps output/input slots and skips the inserted domain parameter. Collection remains indexed by actual first-order formulas.

The spine moves existing generic mathematics into four Core modules and retains old quotient adapters under their public namespaces. Native Replacement and the spine both edit `InductiveAttempts`/`InductiveAttemptsCore` and `KQ1ZF`; applying their complete overlays in succession would lose part of the intended import cut. Keep the spine's Core imports, add native `KQ1ReplacementNative`, and merge the native Replacement calls into `KQ1ZF`.

The following independent static census belongs to the **exact reviewed phase22-v2 source snapshot**, specified by source-map SHA-256 `4096334f8a48fef5ab706297cf628fc3d858055c0acdd5c3cf2d618a5a1c62c0`. It is not a count of the final v3 bytes after the unused-premise cleanup.

| Selection | Project modules | Source bytes | Physical lines | All affected maintained-source delta |
|---|---:|---:|---:|---:|
| Reviewed phase22-v2 snapshot | 179 | 1,768,074 | 37,966 | — |
| Snapshot + native Replacement | 178 | 1,762,012 | 37,842 | +3,902 bytes / +84 lines |
| Snapshot + generic spine | 172 | 1,742,628 | 37,457 | +1,152 bytes / +46 lines |
| Snapshot + deliberately merged spine/native | 172 | 1,739,532 | 37,389 | +4,696 bytes / +120 lines |

The merged projection removes **28,542 bytes / 577 lines** from that selected import closure. These overlapping savings are not additive, and the retained compatibility layer increases total maintained source. The census excludes toolchain libraries and measures imports, not declaration use, proof-object size or checking time. The owned census reproduces the packets' older 174-module baseline before comparing the new snapshot.

The accepted v3 cleanup touches `KLowerQHyp`, which the spine also rewrites, and changes positional calls elsewhere. Future adoption must merge edits into these cleaned sources, preserving their argument counts and underscore witness positions. Copying old whole-file overlays could restore warnings or stale calls. Recompute the census after merging and compile both Core consumers and retained compatibility clients.

## Recommended Lean sequence

1. Preserve the accepted phase22 checkpoint and its two stopped Lean prefixes; pursue the following Lean leads separately from that production acceptance.
2. Prepare the native Replacement/Core combination against those final sources, with the deliberate merge above; check public types, exact axiom profiles and compatibility before claiming the projected import cut.
3. Build one mixed semantic-coverage pilot using `framed-control`, the current decoder prefix and a total caller-or-fallback classifier. Measure complete replacement cost, including the new helper/data modules, before retiring existing site proofs.
4. Keep a small qualitative scheduler-sharing experiment independent. Treat the decrement-fork lemma and direct-program decoder induction as separate optional Lean components; avoid importing the old snapshots or broadening the first integration into a new compiler algebra.

No packet changes the literal machine, supplies unconditional nonhalting, or adds an internally encoded PA/ZFC endpoint. Source-only review, recorded component checks and final production acceptance remain distinct.

A [three-module control-classifier pilot](leads/README.md) now states the exact
ordered caller catalogue and the open full-edge/fallback obligations. It remains
uncompiled and outside the production-source acceptance scope.
