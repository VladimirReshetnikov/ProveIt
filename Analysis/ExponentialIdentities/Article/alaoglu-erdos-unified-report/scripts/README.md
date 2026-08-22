# Exact mixed-block cascade experiments

These scripts reproduce exact 2-adic and 3-adic computations for the mixed
block determinant

```text
D_T = det(((2^n_k M^k)^u_j (3^n_k A^k)^v_j)_(k,j)),
n_k = T - floor(k log_2 M).
```

The columns `(u_j, v_j)` are the first `N` points of `ℕ²` in increasing order
of `u + log_2(3) v`, where `N = 1 + floor((T + 1) / log_2 M)`.

The scripts have no third-party dependencies. All discrete choices are exact:
powers of `M` determine the floors, and the columns are ordered by the
distinct integers `2^u 3^v`. Determinant valuations are computed by exact
elimination over `ℤ/p^Rℤ`; the verifier independently checks small cases with
the fraction-free Bareiss algorithm.

Important: these are synthetic cross-coprime experiments. The inputs satisfy
`gcd(6MA) = 1` and `β = log₂ M`, but `A` is **not** asserted to equal
`3^β`. That missing equality is precisely part of the unknown arithmetic
situation, so numerical output is reconnaissance rather than evidence for the
existence of a counterexample.

Run the independent verifier:

```bash
python3 Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/scripts/cascade_verify.py
```

Print the representative compact table:

```bash
python3 Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/scripts/cascade_experiments.py \
  --M 5 --A 7 --T 30 100 300 --table
```

Inspect the tropical layers near the final valuation. The first command shows a
nonminimal layer beating the first fiber initial form; the second shows a carry
between two layers of the same effective valuation:

```bash
python3 Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/scripts/cascade_layer_report.py 30 5 7
python3 Analysis/ExponentialIdentities/Article/alaoglu-erdos-unified-report/scripts/cascade_layer_report.py 20 11 5
```

For `cascade_experiments.py`, `e2` and `e3` mean `v_p(D_T) - tau_p`,
`U2` and `U3` are the unit-ordering guaranteed gains,
and `I2` and `I3` are the exact first-fiber Vandermonde valuations.
