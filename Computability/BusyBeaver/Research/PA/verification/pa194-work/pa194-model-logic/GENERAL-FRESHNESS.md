# General seeded compiler freshness field

`simRuleAllFresh_generalSeed` proves the full numerical
`CutValidity.Sim.ruleAllFresh` implication for any source-sequent member under
`SeedAdmission 0 reserve e (allIntro s p d)` and the stated source-sequent
validity and membership premises. `simRuleAllFresh_generalRanked` instead uses
ranked admission and an empty initial bound stack. Models satisfy PRA and IΣ₁;
codes and recursive binder depths may be nonstandard.

The proof establishes target equivalence between fixed translations at
`base` and `base + 1` by bounded-depth internal Σ₁ induction. At binders it
combines the induction hypothesis, arbitrary-depth observational transport,
quantifier conversion and label freshness. The rule node supplies the reserve
budget from the source code bounds.

This discharges one complete seeded compiler field. Other quantified rules, a
complete `Sim`, PA identification, physical-machine synchronization and both
consistency directions remain open. `check-general-freshness.sh` replays the
source closure and checks nine axiom reports. Retained objects and workspace
foundations require their own provenance.
