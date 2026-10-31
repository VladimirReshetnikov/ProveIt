# Formula-set witness bounds in candidate-PRA models

`PRAWitnessFormulaSetCandidate.wb_isFormulaSet_sigma` and `wb_isFormulaSet_neg_pi` compose the conditional formula-set lemmas with the corresponding semiformula bounds, discharging those hypotheses in every candidate-PRA model. `WB M φ` asserts in the Lean metatheory the existence of a monotone bound function for that particular model; it does not by itself name a primitive-recursive bound code. These local results are not a complete Foundation refutation-predicate bound or a proof of the PRA consistency equivalence.

The focused author run `/tmp/pra-witness-formulaset-candidate-r5hy0vr8` passed both modules and `#print axioms` checks, which report only `propext`, `Classical.choice` and `Quot.sound`. The driver pins the source files, Lean compiler, 579 selected parent object bytes, and observed direct sources before and after compilation. Its mixed parent includes the experimental FormulaFunctions chain; the hashes authenticate object bytes, not their complete source provenance. Lake fallback and Foundation/Mathlib/package transitive ancestry remain inherited. Private same-parent replay `/tmp/pra-witness-formulaset-candidate-ya4c2941` passed with both source/object/full-log rows matching; its evidence is in `private-evidence/`. A coherent source-current rebuild and independent root replay remain necessary.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-witness-formulaset-candidate-author-replay/replay.py
python3 Computability/DiophantineConsistency/reviews/pra-witness-formulaset-candidate-author-replay/compare.py /tmp/PEER_ROOT
```

Author state, source snapshots, and complete logs are in `author-evidence/`.

The independent root replay `/tmp/pra-witness-formulaset-candidate-nk15ulfx`
also passed; `compare.py` matched both source/object/full-log rows. Its state,
source and logs are in `root-evidence/`; the mixed parent remains inherited.
