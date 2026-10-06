# Exact finite verification

Run from the package directory:

```sh
python3 code/verify.py
```

Python 3.10 or later is sufficient. The script uses only the standard library.
It can also be invoked by absolute path, and it accepts `--output-dir PATH`.
For a shorter preliminary run, use `--max-n 4`. The default completes the full
enumeration through dimension 5.

## What is checked

For every self-dual map `f : {0,1}^n -> {-1,+1}` in dimensions `n=1,...,5`,
the script computes `R_f(x)`, in tail-count form, by iterated Hamming erosions
of its two sign classes. Here `R_f(x)` is the minimum number of coordinate
changes required to change the output. Consequently `R_f >= 1` and the tail
convention is `rho_f(r) = P(R_f > r)`. The vertex distribution is uniform.

The exact maximum of every tail is compared with

```
rho*_n(r) = 2^(1-d) * sum(binomial(d,j), j=0,...,(d-1)/2-r),
d = n if n is odd, and n-1 otherwise.
```

A sum with negative upper endpoint is zero. An explicit majority on `d`
coordinates is checked to attain every budget simultaneously.

For each map and every prefix length `m`, all prefix assignments are examined
to obtain `alpha_m = ||E[f | first m coordinates]||_infinity`. The script checks

```
alpha_m <= P(R_f <= m),                           0 <= m <= n,
alpha_m <= (2^m/V(m,r)) * P(R_f <= r),            1 <= r <= m <= n,
V(m,r) = sum(binomial(m,j), j=0,...,r).
```

The second bound includes `alpha_m <= (2^m/(m+1)) P(R_f <= 1)` at `r=1`.
At `r=m` it coincides with the first bound.

All comparisons use integers. Floating-point arithmetic is not used.
As an independent implementation audit, for every map through dimension 4
the script also directly computes each vertex's minimum Hamming distance to
the opposite sign class and compares the resulting tails with the bitset
erosions. These direct checks explicitly verify antipodal self-duality too.

There are `2^(2^(n-1))` self-dual maps in dimension `n`, hence **65,814 maps**
in the full run. Choosing one sign independently in each antipodal pair
generates each map exactly once. The zero-length and full-length prefix
cases are included explicitly. First `m` coordinates mean coordinates
`0,...,m-1` in the integer representation of vertices.

## Generated files

- `data/exact_verification.json`: machine-readable dimensions, map counts,
  exact robustness maxima, equality counts, and all larger-dimension tables.
- `data/majority_table.csv`: exact fractions and display decimals for selected
  budgets in dimensions 3, 5, 9, 25, and 101.
- `data/majority_table.tex`: a compact LaTeX table for dimensions through 25.
  The complete exact entries for dimension 101 are in the CSV and JSON.
- `data/verification_run.txt`: the actual successful run's printed report.

The larger-dimension table evaluates the explicit binomial formula exactly;
it does **not** enumerate all maps in those dimensions. The computational
checks are finite evidence and do not replace the article's mathematical
proofs. No random sampling is used anywhere.
