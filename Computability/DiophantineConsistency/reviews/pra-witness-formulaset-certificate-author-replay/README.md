# Candidate-PRA formula-set bounded-witness implications

`PRAWitnessFormulaSetCertificate.PRA_proves_of_wb` turns a model-wise `WB` hypothesis for a unary arithmetic formula into an actual candidate-PRA proof of the universally closed translation of `φ(s) → ∃ w, bnd φ(s,w)`. Its two corollaries discharge that hypothesis for the actual Foundation set-language formula-set sigma and negated-pi formulas. The existential witness is not a specified uniform primitive-recursive bound. These theorems do not establish the complete Foundation ZFC refutation-predicate bound or the requested PRA equivalence.

The author run `/tmp/pra-witness-formulaset-certificate-stb7rx9v` passed both modules and all three axiom checks, reporting only `propext`, `Classical.choice` and `Quot.sound`. The driver pins both source files, the Lean compiler, 580 selected parent object bytes, and observed direct sources before and after compilation. Its mixed parent includes an experimental FormulaFunctions chain; these hashes authenticate selected object bytes, not their complete source provenance. Lake fallback and Foundation/Mathlib/package transitive ancestry remain inherited. Private same-parent replay `/tmp/pra-witness-formulaset-certificate-uxc5izmc` passed with both source/object/full-log rows matching; its evidence is in `private-evidence/`. A coherent source-current rebuild and independent root replay remain necessary.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-witness-formulaset-certificate-author-replay/replay.py
python3 Computability/DiophantineConsistency/reviews/pra-witness-formulaset-certificate-author-replay/compare.py /tmp/PEER_ROOT
```

Author state, source snapshots and full logs are in `author-evidence/`.

The independent root replay `/tmp/pra-witness-formulaset-certificate-f8vsj2tp`
also passed and matched both source/object/full-log rows. Its state, sources
and logs are frozen in `root-evidence/`. This retains the same mixed-parent
and existential-witness qualifications.
