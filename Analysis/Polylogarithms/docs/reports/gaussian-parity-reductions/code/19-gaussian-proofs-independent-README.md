# Independent derivations and numerical checks

Run from the package root:

```sh
python code/run_independent.py --quick
python code/run_independent.py
```

The second command performs the full run. The runner also works when invoked
by its absolute path from another working directory. It locates every input
and output from `__file__`; no original research workspace is required.

These programs use Python, SymPy, and mpmath. The recorded runs used
SymPy 1.14.0 and mpmath 1.3.0. Each program can also be executed separately;
the programs that write data accept `--output` or `--outdir`.

## Coverage

| Program group | Exact checks | Independent numerical checks in the full run |
|---|---|---|
| `parity/` | Weight-six and weight-eight ODE derivations; 12 ODE/Bernoulli row comparisons; 100 complex/real formula comparisons; four mixed symbolic identities | All 12 Gaussian rows at 90 working decimal digits, plus all four mixed rows at 60 digits |
| `one_two/` | All 24 real/imaginary polynomial rows at weights four, five, and six, with rational coefficients and assigned-weight checks | All 24 exported rows at 100 digits; 112 logarithmic-moment comparisons through weight eight at four arguments; 30 direct nested-series comparisons; five separately transcribed formulas |
| `audit/` | 160 exact rational cases of the uniform radius prescription | 15 polygamma component checks and the sign/diagonal corrections at 90 digits |

The runner checks subprocess exit codes, required output files, row coverage,
working precision, and numerical residual thresholds. Per-program logs and
the quick/full run summaries are written under `results/independent/`.

The original six verified JSON outputs are preserved without alteration in
`results/independent/{parity,one_two,audit}/reference/`. Regenerated results
are written beside those directories. The four mixed-row quadrature results,
which originally appeared only in terminal output, are now also recorded in
`results/independent/parity/mixed_checks.json`.

Symbolic equalities and rational-bound checks here use exact arithmetic.
Quadrature residuals provide independent numerical cross-checks; they are not
rigorous interval certificates. These scripts do not call the main Hölder
certificate evaluator. For exact enclosure replay, use the separate
`code/replay_certificates.py` program and the accompanying article.
