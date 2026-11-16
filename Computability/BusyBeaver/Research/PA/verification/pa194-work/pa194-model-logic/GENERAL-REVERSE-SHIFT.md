# General reverse shift for seeded translations

`simRuleShift_generalSeed_valid` proves the target implication for any internally valid source formula in the premise sequent under admission at the actual shift node; `simRuleShift_generalSeed_set` takes validity of the entire premise sequent. `simRuleShift_generalSeed_derivation` derives that validity from an actual source derivation for any Δ₁ source theory. These hold for models of PRA plus IΣ₁, including nonstandard syntax and derivations.

The existing `CutValidity.Sim.ruleShift` field does not expose source validity, so this does not yet inhabit that field. It does not construct a full compiler simulation, identify PA, connect to the physical machine, or prove a consistency direction.

Independent incremental replays of the reverse shift and derivation wrapper passed without `sorryAx`, against separately source-replayed shift and freshness baselines, with workspace dependencies retained prebuilt. Run `check-general-reverse-shift.sh --out OUTPUT` for the repository source-closure audit; its workspace foundations remain retained as documented by `check_bridge.py`.
