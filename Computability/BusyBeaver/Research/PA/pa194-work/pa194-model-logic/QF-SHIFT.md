# Quantifier-free compiler shift rules

`quantifierFree_shiftBridge` proves that the coded source shift and fixed target
translation commute for every valid internally quantifier-free formula, with
arbitrary bound and free stacks and labels, including nonstandard codes. Its
proof uses internal Σ₁ structural induction and the atomic and Boolean shift
equations. `simRuleAllShift_quantifierFree` supplies the universal-rule shift
implication without admission assumptions; `simRuleShift_quantifierFree`
supplies the reverse implication under `DepthAdmission` for push/pop.

Quantified descendants, a complete simulation, PA identification, and both
machine/consistency directions remain open. `check-qf-shift.sh` replays the
source closure and checks three axiom reports. Retained objects and workspace
foundations require their own provenance.
