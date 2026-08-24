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

## Rigorous near-curve certificates: `near_curve_certificate.py`

Replaces the earlier, deliberately naive `near_curve_search.py`. Requires
`python-flint` (Arb ball arithmetic and `fmpz_mat.lll`).

A polynomial `P` with integer coefficients restricts to the curve `Y = X^log_2 3`
as `F(t) = P(2^t, 3^t) = sum c_ij exp((i log 2 + j log 3) t)`. The block
`[t0, t0+delta]` is centred and rescaled, `exp(y w)` is expanded exactly in
Chebyshev polynomials through the Bessel identity
`exp(y w) = I_0(y) + 2 sum_{n>=1} I_n(y) T_n(w)`, and the truncation is bounded by
explicit tail columns using `I_n(y) <= (y/2)^n I_0(y)/n!`. All of it is evaluated
in Arb balls, so a reported bound `< 1` is a **proof** that `sup |F| < 1`, hence a
proof that the block carries at most `|S| - 1` points of
`Sol = {t : 2^t, 3^t both integers}` (Chebyshev-system fewnomial budget).

LLL is used only to *find* candidates; every candidate is re-certified from
scratch, so lattice rounding cannot corrupt a result.

`r` independent certified polynomials on one support give a rank-codimension trap:
the block carries at most `|S| - r` points. Since `t = L` and `t = L+1` are always
in `Sol`, `r <= |S| - 2`, and a certified capacity-2 trap on `[L, L+1]` proves

    2^x, 3^x integers, x not an integer  ==>  x > L.

Commands:

```bash
python near_curve_certificate.py verify          # re-verify the stored certificates L = 1..18
python near_curve_certificate.py sweep 1 2 3     # smallest |S| per unit block
python near_curve_certificate.py trap 20 90      # capacity-2 trap  ==>  x > 20
python near_curve_certificate.py verify-trap near_curve_trap_L12.json
python near_curve_certificate.py falsify         # trap never under-counts
python near_curve_certificate.py shapes 8 18     # sparse vs dense supports
python near_curve_certificate.py cover 8         # covers are strictly worse
python near_curve_certificate.py long 8          # longer blocks
```

Data files: `near_curve_certificates.json` (one certificate per block `L = 1..18`),
`near_curve_trap_L*.json` (full certified families for the capacity-2 traps).
