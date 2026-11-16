# Generic numerical compiler with an axiom supplier

`numericalSeedSim` constructs the complete numerical `ShiftValidity.Sim` for any Δ₁ theory T of the relational source language, once supplied with a `SeedCompilerAdmission 0 reserve` and an internal axiom supplier. The axiom supplier must prove the numerical target implication `tr e p → 1` for every model-valued e, s, p satisfying `SeedAdmission 0 reserve e (axm s p)` and `p ∈ T.Δ₁Class`. All logical compiler fields are discharged without additional formula-shape assumptions.

`numericalSeed_refutation_target` uses the canonical seed and its bounded admission to derive `TargetProvable 1` from any internal proof of falsum from T, given a single axiom supplier uniform in reserve. No simulation, initial environment or bound is assumed separately. It applies to nonstandard proof codes in source models satisfying PRA and IΣ₁.

This theorem has not supplied or identified a PA theory/axiom supplier, and does not prove scheduler or physical machine halting, a native iPRA theorem, or the requested consistency equivalence. The concrete finite-adjunctive simulation is a separate instance.

The incremental replay rebuilds the generic simulation, generic refutation wrapper and combined QF-import audit top against previously source-replayed adjunctive simulation and its dependency overlays. Two principal axiom reports have no `sorryAx`; other workspace objects remain prebuilt.

The independent incremental replay passed against separately source-replayed adjunctive simulation and dependency overlays, with workspace objects retained prebuilt. Run `check-generic-sim.sh --out OUTPUT` for the repository source-closure audit and two axiom reports; `check_bridge.py` documents retained workspace foundations.
