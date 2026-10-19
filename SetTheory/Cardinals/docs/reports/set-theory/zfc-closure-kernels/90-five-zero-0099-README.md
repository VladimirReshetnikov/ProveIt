# Combining prior AX symmetries with the new physical dictionary

This supplemental experiment uses `source_model.py` and `data/original203.json` from the incoming `zfc-axiom-symmetry-20261018` package. Their bytes and original provenance are retained. The prior package supplied the logical family of complete AX-row permutations and per-row variable-role permutations. This folder does not reprove those prior theorems or certify a new machine.

The new script identifies the immutable AX word with a prefix, eight axiom rows, and the fixed tail using the canonical 30-atom normalization. It checks the original word against that exact decomposition. It then searches 1,500 source variants using existing physical atoms and grammar subwords while preserving their entry orientation masks.

The best seed has 131 grammar rules. It swaps `a` and `b` in the Łukasiewicz row and preserves the original order of the eight rows. One additional source reassociation makes its abstract source maximum zero run six without changing the 131-rule count. A bounded 700-second follow-up anneal made 15,245,326 proposals and retained 131 rules. This does not improve the fixed-source 128-rule baseline.

These candidates contain an explicit `source_replacements` map. They must not be passed to a checker that assumes equality with the original source word. Their inherited `properties` field is not a certificate; the independent fixed-source checker deliberately refuses changed-source inputs. A complete continuation would need the prior symmetry calibration composed with the new source semantics, an adapted compiler, source relation, runtime proof, and blank-start certificate.

To replay the source seeding experiment, run the script from an empty working directory so its output does not overwrite frozen evidence:

```sh
python3 /absolute/path/to/research/grammar/axiom_symmetry/semantic_axiom_seeds.py 1500
```

The script uses Python's standard library and writes `axiom-canonical-best.json` in the current working directory. The copied upstream source model keeps its original attribution; the canonical dictionary parsing and this combination experiment are new work.
