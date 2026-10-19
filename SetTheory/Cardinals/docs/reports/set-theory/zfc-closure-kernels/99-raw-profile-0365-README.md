# Combined source-family screens

The exact source targets are ordinary numerical-calculus transformations. Their static grammar outcomes do not constitute new consistency machines. The integrated report's source-search section supplies the selector proof, parameter-realizability argument and scanner failure boundary.

- `combined_variants.json`: 32 anchored equality orientations times DNE masks 0, 32 and63, giving96 targets.
- `genc_parameter_variants.json`: 48 independent schema-parameter/order targets and48 versions with GEN's binder changed from `a` to `c`.
- `screen_valid/`: the completed32 DNE32 orientation screens, all passing the54-lock structural auditor; minimum128 rules.
- `genc_screen/`: ten ordinary targets pass structural checks with128–132 rules; eight GEN-c outputs fail the required zero-six condition.
- `gen_c_diagnostic.json`: records the essential assertion and inadmissible-seed limitation of those eight searches.
- `seeds/` and `genc_seeds/`: exact discovery inputs and continuation states.

The initial failed invocation with an RNG seed outside the C++ integer range is not included as a completed search. The stored screens use valid integer seeds. Time-bounded iteration counts need not reproduce on different hardware; the candidate audits do.

The top-level `reproduce.py` already regenerates the two complete target families from an isolated extraction of the pinned input archive.

To prepare the full inherited machine-search environment and C++ optimizer for additional experiments:

```sh
python3 -B source_search/prepare.py
```

Then, from the archive root:

```sh
python3 -B source_search/generate_combined.py --output /tmp/combined-targets.json
python3 -B source_search/generate_parameter_targets.py --output /tmp/parameter-targets.json
python3 -B source_search/search_combined.py --only-dne32 --seconds 8 --output /tmp/orientation-screen
python3 -B source_search/search_combined.py --seeds source_search/genc_seeds --max-initial 132 --seconds 12 --output /tmp/parameter-screen
```

The script defaults point to `source_search/build/zfc-below245-source-search-20261018` after preparation. The inherited full package's source-generation and seeding tools are also available there. Its independent auditor retains the required scanner assertion; the diagnostic GEN-c failure is not patched into an acceptance rule.

The copied `converse_encodings.tex` and `axiom_permutation_lemma.md` are inherited proofs used by the new combinations. Their original attribution is preserved. Only the explicit combination generators and bounded screening wrapper are new in this directory.
