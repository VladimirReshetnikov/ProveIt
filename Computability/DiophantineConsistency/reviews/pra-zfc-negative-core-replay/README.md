# Actual ZFC negative pi derivation-core witness bound

The frozen 35-module suffix builds and checks all ten literal pi-rule
branches, their witness-bound helpers, the formula-set left conjunct, the
complete general negative pi core conditional only on the negative pi axiom
recognizer bound, and the ZFC specialization
`PRAWitnessZFCNegativePiCore.wb_neg_zfcCorePi`. The specialization discharges
the theory-specific hypothesis using the already checked `goodCh_zfc`.
For every candidate-PRA model it proves `WB` for the negation of the *actual*
Foundation ZFC derivation-core pi formula. It makes no assumption that such a
model satisfies `IΣ₁`, and does not assert that the `WB` majorant is a uniform
primitive-recursive code.

Each branch identity and the assembled pi-tail identity is checked by `rfl`
against Foundation's source definitions. The final axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Author and independent peer
both pass, with all 35 source, object and log hash rows identical.

```
python3 Computability/DiophantineConsistency/reviews/pra-zfc-negative-core-replay/replay.py
```

The parent is the independently replayed ZFC axiom-witness closure, itself over
the independently replayed 214-module full local-project source closure. The
script guards 219 parent project objects, 35 frozen sources and 23 direct
external objects, and rejects Lean errors, warnings and `sorryAx`. At author
completion all 214 base project sources, nine ZFC/project suffix sources, and
35 negative-core sources matched the workspace; this is time-specific. The
transitive ancestry of Foundation, ZFCinPA Instances, mathlib, toolchain and
other packages remains inherited. Positive sigma core, outer refutation bound,
and the final HA equivalence require their own completed integrations.
