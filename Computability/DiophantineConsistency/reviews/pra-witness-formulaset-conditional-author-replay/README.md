# Conditional set-language formula-set witness bounds

`PRAWitnessFormulaSet.wb_isFormulaSet_sigma` and `wb_isFormulaSet_neg_pi` lift the corresponding witness-bound assumptions for the actual Foundation set-language semiformula recognizer to its formula-set recognizer, for an arbitrary model of arithmetic PA-minus. These are explicit hypotheses; this packet does not establish the semiformula witness bounds or the overall PRA consistency equivalence.

The author build `/tmp/pra-witness-formulaset-conditional-_npiedco` passed and checked both theorems, with `#print axioms` reporting only `propext`, `Classical.choice` and `Quot.sound`. `manifest.json` pins the two sources, Lean compiler, 559 selected object bytes in the provisional parent and the observed direct source files; the replay rechecks them before and after compilation. The recorded parent bytes are **not** authenticated as the result of those observed source files: the provider and its transitive ancestry are provisional. Other Foundation, Mathlib, Lean package objects and the Lake `LEAN_PATH` fallback remain inherited. A fully coherent source-current replay is still required.

Run an independent focused replay and compare its output:

```sh
python3 Computability/DiophantineConsistency/reviews/pra-witness-formulaset-conditional-author-replay/replay.py
python3 Computability/DiophantineConsistency/reviews/pra-witness-formulaset-conditional-author-replay/compare.py /tmp/PEER_ROOT
```

The author state, source snapshots and complete logs are in `author-evidence/`. The private same-parent replay `/tmp/pra-witness-formulaset-conditional-7czxijmk` also passed; both source/object/full-log rows match. Its state, source snapshots and logs are in `private-evidence/`. A separate root replay is underway.

The independently launched replay
`/tmp/pra-witness-formulaset-conditional-ekk5t78l` also passed; `compare.py`
matched both source/object/full-log hashes. Its state and logs are frozen in
`independent-evidence/`. It uses the same provisional parent and does not
discharge either semiformula hypothesis or authenticate the inherited closure.
