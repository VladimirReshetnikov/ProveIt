# Exact semantic reference implementation

`finer_reference.py` implements finite algorithms used in the report with only
Python's standard library. Rational arithmetic uses `fractions.Fraction`.

These programs are **not** an iPRA proof checker and are not evidence that a
Lean theorem has been kernel-checked. Their purposes are:

1. make certificate formats executable;
2. provide regression fixtures for the later Lean implementation;
3. catch off-by-one, encoding, and replay mistakes early.

Run:

```bash
PYTHONPATH=reference python3 -m unittest -v reference/test_finer_reference.py
PYTHONPATH=reference python3 reference/generate_examples.py
```

The test suite covers mixed-radix coding, least search, cyclic demand closure,
least prefixed points, backward viability, exact/metric observers, tree error
accumulation, height-bounded enumeration, and exact rational cubic bisection.
