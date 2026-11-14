# Portable local encoding and macro experiments

All scripts use Python's standard library. Run them from this directory:

```sh
python3 -B gate_variants.py --output gate_variants.json
python3 -B membership_transpose_config.py
python3 -B orientation_recoding.py
python3 -B transposed_implication_macro.py --output transposed_implication_macro.json
python3 -B implication_transpose_words.py --output implication_transpose_words.json
python3 -B head1_countermodel.py
```

Each script raises an exception if one of its implementation checks fails.
`THEORY.md` states the ordinary mathematical arguments and their limits.
The JSON receipts contain exact words, source subtrees, and finite results.
No script compiles or certifies a binary Turing machine, and no machine below
196 states or internal PA consistency theorem is asserted by this directory.

`membership_config.json` is the 11-symbol input family for the parent's
physical grammar search. Its header contains only the variable constructor,
head, and gate data; the parent's fixed machine rows and macro attributes must
be retained when using it with that search implementation.
