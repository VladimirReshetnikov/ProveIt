# Final PA composition: reviewed source, pending compilation

The [draft](BinaryConsistencyRotation240.lean) connects the existing fixed
binary halting sentence to `RotationInterpreterConsistency240.rotationHaltsSentence`,
then transfers the upstream IΣ₂ and PA consistency theorems for ZF and ZFC.
It identifies the packed table and physical seed explicitly and adds no
consistency or simulation premise. Its [audit draft](Audit.lean) has eight
named probes and ten typed callers.

**This draft has not been compiled.** The [source/API review](source-review.json)
found no mathematical or interface issue; that review supplies no compiler
result. The separately checked [blank/control equivalence](../../arithmetic_blank_control_rotation240.md)
is already published, with both clocks internal to arbitrary IΣ₁ models.

The [upstream inventory](upstream-inventory.json) records the remaining
verification work at its snapshot: the unchanged register endpoint has
11 modules without current recorded compiled providers, with 71 existing
pairs reusable. The full W7 import closure has 88 such modules: those 11,
76 validator predecessors and the W7 facade. The
[inventory review](upstream-review.md) lists the register modules, retained
proof limits and external dependency gaps; the
[validator plan](validator-route-plan.json) gives its dependency order.
These are gaps in fresh local verification, not findings that the source
proofs are false.

After that inventory, [R2Neg](../../../../../../Logic/Interpretability/ZFCinPA/r2neg.md),
[R2Quant](../../../../../../Logic/Interpretability/ZFCinPA/r2quant.md),
[R2Main](../../../../../../Logic/Interpretability/ZFCinPA/r2main.md),
[R2Gic](../../../../../../Logic/Interpretability/ZFCinPA/r2gic.md),
[NativePeel](../../../../../../Logic/Interpretability/ZFCinPA/native_peel.md),
[internal renaming/substitution](../../../../../../SetTheory/BoundedConsistency/internal_soundness_check.md),
[coded-derivation soundness](../../../../../../SetTheory/BoundedConsistency/coded_derivation_check.md),
[internal ranks and bounds](../../../../../../SetTheory/BoundedConsistency/coded_rank_check.md),
[ZFC axiom codes](../../../../../../SetTheory/BoundedConsistency/axiom_code_check.md),
[partial universe truth](../../../../../../SetTheory/BoundedConsistency/universe_truth_check.md),
[fixed-level truth and calculus soundness](../../../../../../SetTheory/BoundedConsistency/level_soundness_check.md),
[internal ZFC axiom truth](../../../../../../SetTheory/BoundedConsistency/axiom_truth_check.md),
the [compactness/completeness interfaces](../../../../../../Logic/FirstOrder/checked_interfaces.md)
and ten [register-program modules](../../arithmetic_register_prerequisites.md)
passed. NativePeel required one
implicit-argument correction, with the failed original run preserved.
The [first concrete bisimulation check](../control-bisim-first-check/README.md)
hit the 4 GiB memory limit; the
[complete split certificate and assembled equivalence](../../control_bisim_rotation240_split.md)
now pass under the unchanged cap. These fresh checks remove twenty-eight of
the 88 entries. The
[provider review](../../../../../../Logic/Interpretability/ZFCinPA/fixedpoint-template-route/README.md)
also identifies an already accepted current-source result for
`ModelCodedPredicateTemplate`; its exact source/object pair is reusable, with
the original warnings and legacy capture limits retained. This closes one
further entry without replay: 29 resolved and 59 remaining.
An independent [legacy-record reconciliation](../../../../../../Logic/Interpretability/ZFCinPA/fixedpoint-template-route/legacy-review.json)
confirms that reuse and finds no further omission among 1,511 named PASS
records. Its counts describe its earlier scan checkpoint; the two later
soundness/axiom-truth checks are included in the current count above.
All eleven register-side entries are now checked;
the [register endpoint](../../arithmetic_register_endpoint240.md) includes
validator acceptance iff Rotation240 control halting from the exact seed.
The common helper and 31 leaf modules are
additional checked modules, outside that original inventory.
The [Foundation Z dependency branch](../../../../../../Logic/Interpretability/ZFCinPA/foundation_set_theory_check.md)
now also has fresh Model, Basic, ExistsUnique and Z checks, with the cached
library boundaries explicitly retained. These external dependencies do not
change the original 88-project-module census.
Subsequent actual records must update the remaining work; the frozen
inventory itself stays unchanged. Checks retain
the upstream source's declared limits and known warnings, while new audit
files use default proof limits. Previously checked parents need not be replayed.

The [publication record](publication.json) binds these source-only artifacts.
The [history](history.json.gz) preserves the author plans, independent review,
inventory scripts and frozen receipts. No future proof object or successful
run is asserted by this package. Final compilation and axiom auditing remain
required before publishing the PA endpoint as checked.
