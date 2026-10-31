# Positive simple derivation-rule witness bounds

`PRAWitnessPositiveSimpleRules` extracts the identity, verum, weakening and shift leaves directly from the sigma disjunction of Foundation's `Derivation.blueprint T`; each extraction is proved equal by `rfl`. For arbitrary candidate-PRA models, it proves `WB` for each actual leaf, using existing graph witness bounds and explicit domination of the remaining existential witnesses. `WB` supplies a monotone bound separately in each model; these four leaves do not establish the whole sigma core, a uniform primitive-recursive code, or the requested PRA equivalence.

The author run `/tmp/pra-witness-positive-simple-rules-kw9hkksw` passed source, checks and final reauthentication. It pins 600 selected parent object bytes, sources and Lean compiler. The parent is the exploratory set-shift/FormulaFunctions composition, whose complete source ancestry has not been authenticated. Its `PRAWitnessSetTerms` source was subsequently amended to fix an existing warning; this run is a prior provider snapshot and is not a source-current closure proof. Foundation and external package transitive ancestry and the Lake path fallback remain inherited. Private same-parent peer `/tmp/pra-witness-positive-simple-rules-z9nzpoj1` passed with matching source/object/full-log rows; its evidence is in `private-evidence/`. Root independent same-parent replay `/tmp/pra-witness-positive-simple-rules-pl3euclp` also passed and matched both rows; its evidence is in `root-evidence/`. A coherent-source replay is still required.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-witness-positive-simple-rules-author-replay/replay.py
python3 Computability/DiophantineConsistency/reviews/pra-witness-positive-simple-rules-author-replay/compare.py /tmp/PEER_ROOT
```

Author state, source snapshots and full logs are in `author-evidence/`.
