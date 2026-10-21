# Combined command-local and partial-selector table: 215 states

This is a held **215-state, 430-row** binary table, with a 202-node source DAG and 4,751 primitive occurrences. Exact source composition, all 4,750 internal decoder prefixes, and all 4,751 primitive entry actions have passed finite checks. Full quantified runtime and calibrated blank-startup checks are pending; this draft does not claim an accepted 215-state consistency machine.

The construction combines the command-local field reader and command permutation from `K216_Permuted_Commands_2026-10-21` with the partial-selector source reassociation of the accepted [216-state machine](../candidate-k216/README.md). The resulting source has exactly the ordered primitive expansion and both complete guarded control-flow graphs of the command-permuted reference. Its maximum path depth is 47 and maximum zero run is six.

The allocation keeps the existing 69/400 continuation fold, the 164/183 partial-selector fold, and the contextual state-172 source repair. It also uses the separately proved three-step replacement `81/0: 0L92 → 0L111`. It changes 35 retained rows relative to the accepted partial-selector 216-state table, deletes state 224, and adds no state labels. The source DAG reduction and the physical state reduction are separately checked.

[proof.md](proof.md) explains the source and physical boundaries. [table_recipe.json](table_recipe.json) and [dag_recipe.json](dag_recipe.json) give deterministic reconstruction data, while [canonicalization.json](canonicalization.json) records the reversible map to working states 0–214 and terminal state 215. `k215.native.tm` preserves native labels; `k215.tm` uses the dense labels.

To reconstruct from the accepted 216-state parent without a solver or runtime checker:

```sh
python3 -B reconstruct.py --parent /path/to/candidate-k216 --out /fresh/output
```

The first allocator gate used one global physical representative per logical node and rejected eight valid old state-108 aliases. That failed record is preserved. A separate local-entry audit checks all eight actual `101` contexts, the unchanged entry rows, and all other prefixes. Its own first audit also required the intentional 81/0 repair to be stated as a three-step equivalence; that correction and a subsequent parser typo are retained in the research history. The machine and source bytes did not change during these audit corrections.

The submitted source transformations and existing machine components retain their original attribution. The composition, bounded allocator adaptation, deterministic recipe, and local-entry review were authored in this repository's Codex research lane. The allocator's inherited engine-row census is only a synthesis filter; it supplies no new universal runtime theorem. No Lean, Rocq, or PA internalization is claimed for this table.
