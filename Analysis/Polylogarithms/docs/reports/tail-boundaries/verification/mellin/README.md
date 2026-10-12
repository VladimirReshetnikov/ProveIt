# Mellin and polylogarithm verification

Run from the bundle root:

```sh
python verification/mellin/verify_mellin_polylog.py
```

Dependencies are Python 3, SymPy, and mpmath. The verifier writes
`mellin_checks.json` beside its own script, independently of the current
working directory. An alternative destination can be supplied with
`--output PATH`.

The default run checks 2,002 exact rational or polynomial identities,
including the shift recurrence, both finite annihilation identities, and
rational negative-order polylogarithm integrals evaluated independently
by the beta integral. It then performs the existing 11 direct quadratures
for positive integer orders and explicit scaled examples at 40-digit
working precision. Assertions terminate the run if a check fails.

The quadratures are numerical diagnostics, not certified intervals. The
article's proofs establish the complex-order formulas and their parameter
derivatives. `NUMERICAL_AUDIT.md` records a separate unsuccessful optional
order-derivative diagnostic; that computation is not counted as a passed
check or included in the default verifier.
