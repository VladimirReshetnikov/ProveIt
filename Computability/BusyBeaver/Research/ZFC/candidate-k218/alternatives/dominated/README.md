# Dominated-rho8 alternative with 218 working states

Source 149 replaces unrestricted numerical rho8 by its instances whose fourth
input satisfies **U≤A**, proves that every native derivable code is preserved,
and compiles a new source with 203 distinct subtrees into an exact 218-state
binary machine. It has 436 transition rows and a separate halt outcome. The
[primary K218](../../README.md) remains a distinct accepted construction;
this alternative is not a 217-state result.

Eight fresh direct checks passed: two independent logical forward checkers,
source reconstruction and an independent full CFG comparison, table reconstruction,
compact relabeling, complete blank startup and all 6,176 universal runtime cases.
The [actual record](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149/actual.json),
[independent actual audit](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149/actual-review.json) and
[full source review](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake191-source149-review.md) preserve the exact scope.

Combining the new ordinary proof with the pinned inherited numerical-calculus/ZFC
calibration gives the ZFC-formalizable equivalence
`blank nonhalting ↔ Con(ZFC)` for this exact table. This is an ordinary reviewed
mathematical result, not a newly compiled exact-table Lean/Rocq or internal PA
endpoint. It does not assert unconditional nonhalting or minimality.

## Exact files and proof

- [Compact table](machine/k218.tm): working labels 0–217, start 0, halt 218.
- [Native table](machine/k218.native.tm): historical labels, start 0, dispatcher 84, halt 254.
- [Complete source](machine/sites218.json): 4,751 primitive occurrences, 203 subtrees, depth 45, maximum zero run 6.
- [Transition recipe](machine/transition_recipe.json): original-baseline edits and exact compact relabeling.
- [Whole startup boundary](machine/boot_boundary.json): all register values, spares and one cells.
- [Proof exposition](proof.md): native numerical domination, source compiler, runtime and stacking boundary.

The logical certificate has 3,728 proof nodes and 5,160 shared terms. A deeper
implication-subterm instance closes the earlier conditional cd59 gap and derives
the literal unrestricted row. The common-input source uses three closed AX
splices and leaves all 186 outside-AX source paths unchanged. Temporary CC4
was used during source search; the delivered final source uses only CC1–CC3.

The freshly checked complete startup takes 312,605 transitions to dispatcher 84
at head −5, gap 80, logical registers `[3,0,0,0,3,0,0,0,0]`, 130 one-valued spare
blocks and 277 exact one cells. The runtime proves 6,176 cases with 1,616,989
symbolic steps, four exact-table list schemas, all 436 rows covered and duration
constants at least 13. Its symbolic derivation represents arbitrary natural
register values and gap, and every nonempty finite list of natural spare values.
Startup and runtime are separate obligations from source/calculus calibration.

## Relation to the other 218-state constructions

The allocation removes native 227 and 228 and adds native 400 relative to its
219-state baseline. Its final source no longer contains the four-occurrence
subtree needed for the second role of the primary/contextual state-85 fold.
The other nine-occurrence role survives. The [literal comparison](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149/source-comparison.json)
therefore rules out directly counting that existing final fold as a second saving;
it does not rule out another allocation or contextual optimization. Different
removed state labels alone do not establish that physical patches compose.

The submitted predecessor is `f8ec6158f3bdc885139ee395ae34fe44c3251b9f`, and the
archive arrived at `7071e5041ee316d087661b658362feed159901ef`. The
[placement map](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-placement.json) and
[recovery/reproduction instructions](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake191-source149-reproduction.md)
retain access to the original report, proof appendices, code and data. The
[source/actual review receipt](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149/review.json) records
full reads and limits. A [second independent mathematical peer](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake191-source149/second-peer/review.json) found no blocker. No manifest wrapper, proof search, ancestor checks or
proof-assistant build was executed in this fresh replay.

Original credit is retained in [NOTICE.md](NOTICE.md), [licenses/](licenses/)
and [provenance/](provenance/). Source 149 contributes the dominated numerical
recovery, source schedule and literal construction. `review_upstream_reflection`
authored this intake exposition, independent literal comparison, selected-check
runner and bounded actual review under root's execution authorization. These
reviews do not claim authorship of the submitted proof or machine.
