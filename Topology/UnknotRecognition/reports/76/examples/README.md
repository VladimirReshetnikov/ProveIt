# Checked source-language examples

These inputs describe abstract disk-patch languages, not embedded knot exteriors.
Each has its original grammar (`.json`), producer-selected table certificate
(`.cert.json`), complete summary/query result (`.result.json`), and independent
checker result (`.check.json`).

- `small_repetition`: sixteen independently chosen strips. A costs 1 and has charge 0;
  B costs -3 and has charge 1. The requested charge 1 forces an odd number of B
  strips. The optimum is -44, with one A and fifteen B strips.
- `huge_repetition`: the same source with W = 2^1024. The optimum is -3W+4.
  The compact witness records one A and W-1 B occurrences without expanding them.
- `mixed_grammar`: width two, separate libraries, equal-span union, a 129th power,
  and a final concatenation. Its fixed physical span is 390.

The producer and checker take the source as a separate argument. A certificate
for a changed source is invalid even if its syntax looks similar. Query sectors
are module sectors; a geometric cap would need its own certified charge shift.

Run from the package root:

```sh
python code/checker.py examples/huge_repetition.json examples/huge_repetition.cert.json
python code/compressed_search.py examples/mixed_grammar.json
```

JSON stores huge exponents as decimal strings; input bit length and decimal
length differ only by a fixed factor. The mathematical repetition parameter is
a literal integer, not a circuit that evaluates to an exponent tower.
