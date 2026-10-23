# Phase22: normalize semantic proofs and reuse the 219 root

**The serial Lean kernel check, independent actual readback, evidence capture
and independent capture review pass.** This continues [phase21](../phase21/README.md)
at `0d335c25cf703d370ceee628a8cb0e722afa2ea0`. The literal 215-state machine and its
halting/nonhalting statements are unchanged. The internal PA endpoint and a
minimum-state theorem remain open.

The nine-source change shares existing proof mechanisms:

- `ConstructibleAbs` normalizes subtype operations before transporting witnesses.
  The five proof edits are Claude's upstream `5a26d6d80568090140d5e4a775837a7769f30ed1`,
  adopted by attributed cherry-pick `d0cb4828f01d05027e23bb8984bdf8f62eb393d4`.
- `ProfileSyntax` and `CompositionModel` replace twelve duplicated witness
  transports by logical congruence. The new `iff_congr_iff` transports the two
  implications constructively; a separate focused fresh audit reports **no axioms**.
- `L2Root219` reuses the existing `L2K` run proofs through `trCore` and iteration
  endpoints through `Dag219.iter_iff`. Every old root declaration statement and
  the `toAS`/`s2` definitions remain exact; its short continuation proof stays local.
- Five tagged/quotient files remove unused section premises and rename unused
  witness binders, without disabling a linter or relaxing the warning gate.

## Source and interface changes

| Source | Before lines | After lines | Bytes removed |
|---|---:|---:|---:|
| [ConstructibleAbs](../../../../../../../Lean/BusyBeaver/ZFC/ConstructibleAbs.lean) | 917 | 911 | +836 |
| [ProfileSyntax](../../../../../../../Lean/BusyBeaver/ZFC/ProfileSyntax.lean) | 180 | 155 | +1,569 |
| [CompositionModel](../../../../../../../Lean/BusyBeaver/ZFC/CompositionModel.lean) | 155 | 133 | +788 |
| [L2Root219](../../../../../../../Lean/BusyBeaver/ZFC/L2Root219.lean) | 236 | 105 | +7,616 |
| [KLowerRaw](../../../../../../../Lean/BusyBeaver/ZFC/KLowerRaw.lean) | 201 | 202 | -13 |
| [KLowerTag](../../../../../../../Lean/BusyBeaver/ZFC/KLowerTag.lean) | 210 | 211 | -11 |
| [KLowerQHyp](../../../../../../../Lean/BusyBeaver/ZFC/KLowerQHyp.lean) | 248 | 251 | +1 |
| [KQ1Model](../../../../../../../Lean/BusyBeaver/ZFC/KQ1Model.lean) | 190 | 190 | -3 |
| [KQ1Basic](../../../../../../../Lean/BusyBeaver/ZFC/KQ1Basic.lean) | 149 | 149 | -1 |
| **Total** | **2,486** | **2,307** | **10,782** |

The nine files remove **179 physical Lean lines / 10,782 bytes**. This includes
ConstructibleAbs's six lines / 836 bytes once. The cleanup itself adds five
`omit` lines and 27 bytes while removing redundant theorem arguments. No new
module or writer is retired and no executable definition or machine data changes.
The independent `ArithmeticL2` lane remains unchanged.

Five signatures become stronger by dropping nine unused section hypotheses:
`KLower.raw_tagged`, `tag_inhabited`, `tsing_tagged`, `tsing_members` and
`tsing_exists`. Their conclusions and proof bodies are retained; ten maintained
calls in `KLowerTag`/`KLowerQHyp` are updated. All fifteen existing typed client
sources remain unchanged.

Four unused `witness` binders become `_witness`: `KQ1Model.member_left_congr`,
`member_right_congr`, `modelSetoid`, and `KQ1Basic.interpreted_pair`. Their
positions and types are preserved, including the quotient witness positions.
External named calls using `(witness := ...)` on these declarations would need
`(_witness := ...)`; the maintained caller census finds none. This is a reviewed
interface change, not a blanket claim that every old printed binder name survives.

The primary 215 endpoint retains **179 project modules** and drops from
1,771,267 to **1,768,101 source bytes** (3,166 fewer). The larger nine-file saving
includes the legacy Root219 facade outside that primary closure. Import-closure
size and maintained-file savings measure different scopes. The
[source measures](integration/metrics.json) bind the exact comparisons.
The metrics and source-spec files retain their original measurement/precheck
status labels. The [final progress record](integration/progress.json), terminal
result and capture reviews record the accepted checkpoint.

## Accepted check and retained attempts

The accepted selected run takes **43.01 seconds** and covers **226 providers**:
211 project modules and fifteen existing typed clients. **56 providers compile
fresh**, 170 reuse exact accepted source/object/dependency/log/toolchain bindings,
and both endpoint audits compile fresh. Six existing clients rebuild through
source transitivity. All fresh providers and both audits have **zero warnings**;
seven inherited warning occurrences retain their accepted meanings.

All 93 client reports, five `WFTheory` reports and ten endpoint-audit reports
retain their exact accepted axiom profiles. The independent actual readback checks
1,177 owner inputs, 68 mandatory present pins and sixteen absences, with 195
adjacent raw provider records. Thirty-one inherited providers retain the accepted
aggregate boundary for absent original raw records; no receipts are fabricated.
The 215 source-forward and site batches retain their exact accepted bindings.
This is not a new certificate-stack check for another machine variant.

Two stopped compiler prefixes remain unaccepted history. V1 exposed added
`propext` from the global `iff_congr`; unchanged theorem statements were not enough
to preserve assumptions. Constructive v2 restored the exact reports, then stopped
on an inherited unused-section-premise warning. V3 applies the reviewed unused-
premise cleanup and passes the unchanged exact-profile and zero-fresh-warning
checks. Neither stopped prefix is counted as accepted validation.

The [terminal result](lean/result.json) has SHA-256
`cd966bd654b04a3c2becbafc00ba1f13f2866fcbab64b5b6715cf6449461dc66`;
the [independent actual readback](lean/result-review.json) has SHA-256
`c749826c11113a0f2c0f9e2f50c77bbe39a76b4f63e4f6de18c986de01c968c8`.
The focused helper audit is one additional fresh invocation, separate from the
226-provider closure and two endpoint audits; it does not expand endpoint scope.

The deterministic capture passes for **443 archive blobs, 719 logical entries,
713 source aliases and 563 raw evidence rows**, with eleven external phase21
historical leaf files and both stopped prefixes preserved. The archive is
**1,357,782 bytes**, SHA-256
`00848017567861ba4337768633ae586929a151751d93ebe905f11511802a95cf`.
The [capture receipt](lean/capture.json) and [index](lean/index.json) identify
content-addressed blobs: source-path aliases and logical names resolve through
the index to blob SHA-256 values. Inspect indexed members as inert bytes; do not
extract or run captured code. Executable proof objects are not shipped.

The [independent capture review](integration/capture-review.json) and
[launch receipt](integration/capture-review-outer.json) pass. The review reconstructs
the complete index and source-alias mapping, checks every archive member, and
checks all 68 present pins and sixteen absences. Phase21's eleven Lean evidence
leaf files remain exact external historical boundaries; only its root README
receives a successor pointer.

The [independent source peer](integration/source-peer.json) also passes. The prior
[source author readback](integration/source-author-readback.json) is preserved
with [its authorship boundary](integration/source-author-attribution.json). Source
receipt v4 counts 75 original ConstructibleAbs declaration headers, including
`codeNF`; it corrects the historical v3 documentary count without changing sources,
compiler receipts or acceptance. The [Lean evidence](lean/README.md) records the
receipt hashes and the separate capture-reader repair.

The [batch219 review](batch219-review.md) compares all eight already placed packets,
separating adopted changes from prospective Lean work and recorded component claims.

The [uncompiled control-classifier lead](leads/README.md) is a source-only research
pilot, outside the accepted production-source kernel check.
