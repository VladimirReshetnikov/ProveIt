# Exact reference algorithms

`kifcr_reference.py` uses only Python's standard library and exact integer or
`Fraction` arithmetic. It implements executable versions of the finite
algorithms used in the report:

- Boolean folds;
- both a pedagogical `(found,witness)` search and the current checked
  `Search.mu` least-zero/sentinel convention;
- bounded traces and invariant checks;
- least reverse demand on DAGs;
- capped monotone cyclic demand closure, rank/fixedness, overflow diagnostics,
  and exhaustive small-box leastness checks;
- backward residual reachability and stable-key deduplication;
- finite relational viability, brute-force suffix comparison, and least paths;
- exact and diameter-stable observers and finite tail budgets;
- guarded finite argmin;
- exact rational bisection for `y^3+y=x`;
- height-bounded enumeration and finite-net error accumulation.

Run:

```sh
python3 -m unittest -v reference/test_kifcr_reference.py
```

The tests are implementation evidence. They are not a proof checker and do not
replace the `Prf PRAAx` construction required by the Lean plan.
