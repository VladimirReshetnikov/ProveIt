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
the [compactness/completeness interfaces](../../../../../../Logic/FirstOrder/checked_interfaces.md)
and ten [register-program modules](../../arithmetic_register_prerequisites.md)
passed. NativePeel required one
implicit-argument correction, with the failed original run preserved.
The [first concrete bisimulation check](../control-bisim-first-check/README.md)
hit the 4 GiB memory limit; the
[complete split certificate and assembled equivalence](../../control_bisim_rotation240_split.md)
now pass under the unchanged cap. Together these results remove twenty-one of
the 88 entries, leaving 67. All eleven register-side entries are now checked;
the [register endpoint](../../arithmetic_register_endpoint240.md) includes
validator acceptance iff Rotation240 control halting from the exact seed.
The common helper and 31 leaf modules are
additional checked modules, outside that original inventory.
Subsequent actual records must update the remaining work; the frozen
inventory itself stays unchanged. Checks retain
the upstream source's declared limits and known warnings, while new audit
files use default proof limits. Previously checked parents need not be replayed.

The [publication record](publication.json) binds these source-only artifacts.
The [history](history.json.gz) preserves the author plans, independent review,
inventory scripts and frozen receipts. No future proof object or successful
run is asserted by this package. Final compilation and axiom auditing remain
required before publishing the PA endpoint as checked.
