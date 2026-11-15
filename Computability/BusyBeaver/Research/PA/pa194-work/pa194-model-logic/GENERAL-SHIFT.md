# General seeded universal shift field

`simRuleAllShift_generalSeed` proves the complete numerical `CutValidity.Sim.ruleAllShift` implication for an arbitrary valid member of the source sequent. Its explicit hypotheses are `SeedAdmission 0 reserve e (allIntro s p d)`, `IsFormulaSet SourceL s`, `∀p ∈ s`, and `q ∈ s`. `simRuleAllShift_generalRanked` requires only `RankedAdmission e (allIntro s p d)`, `simBound e = 0`, sequent validity and `q ∈ s`.

The proof uses `shift_translation_sameBase`, the exact numerical equality of translated source-shift and the original formula with a prepended free-stack element, at the same allocation base. This holds for every internally valid formula, arbitrary model-valued stacks and labels, and arbitrary nesting, proved by a definable internal depth induction. `generalBaseShift_all_codes` supplies the change to the incremented allocation base, with its freshness and reserve bounds discharged from ranked admission at the actual `allIntro` node. The relevant arithmetic model satisfies PRA and IΣ₁, and source syntax may be nonstandard.

This proves a single compiler field under the stated admission invariant; it does not construct a compiler, identify the source theory with PA, or establish the machine consistency equivalence. The reverse shift field currently lacks an explicit formula validity premise in the compiler interface and remains separate.

The independent incremental source replay passed, rebuilding four source modules and the audit top against separately source-replayed general-freshness, observational-general and full-one-level baselines. Workspace and other dependencies remain prebuilt.

Run `check-general-shift.sh --out OUTPUT` from the repository to replay the source closure and check three axiom reports. This replay retains the workspace dependencies described by `check_bridge.py`; it is not a clean rebuild of the whole workspace.
