# Compiler interface with shift-sequent validity

`ConPA.Sequent.ShiftValidity.Sim` refines the existing cut-validity compiler interface by exposing validity of the source premise sequent at `ruleShift`. `Sim.compile` supplies this from the actual source derivation and still exposes cut-formula validity. `Sim.ofCutValidity` converts every old simulation to the refined interface. The general seeded reverse-shift result provides the refined shift implication for valid formulas.

The interface alone supplies no other rule fields and does not construct a simulation, identify the source theory with PA, or connect to the machine. The general compiler assumes IΣ₁, and the concrete seeded translation also assumes PRA; these results are not native iPRA derivations.

The independent incremental replay rebuilt the interface and combined audit against separately source-replayed actual-derivation, shift and freshness baselines, with other workspace dependencies retained prebuilt. `check-shift-combined.sh --out OUTPUT` checks the repository source closure and eleven axiom reports. It retains workspace foundations, as documented by `check_bridge.py`.
