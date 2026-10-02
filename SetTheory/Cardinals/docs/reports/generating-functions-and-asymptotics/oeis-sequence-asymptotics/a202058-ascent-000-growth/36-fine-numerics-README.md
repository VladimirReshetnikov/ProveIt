# Fine-scale numerical investigation of OEIS A202058

Date: 2026-10-02. All files here are new work; the earlier report and research
directories were read but not modified.

## Main findings

Let `mu = 8/(3*pi^2)`, `b_n = a_n/(n!*mu^n)`, and

```
h_n = log b_n
g_n = n (h_n-h_(n-1))
c_n = n (g_n-g_(n-1)).
```

1. `oeis-b202058.txt` is the original b-file downloaded from
   https://oeis.org/A202058/b202058.txt on 2026-10-02, with exact terms 0–176.
   The C++ recurrence independently reproduces all 177 terms and extends exact
   counts through 400. This uses GMP integers, with no numerical rounding.
2. A positive-sum long-double version extends the normalized values through
   1000. Its maximum relative error against exact values through 400 is about
   `3.22e-17`. Terms 401–1000 are **numerical approximations**, not exact counts.
3. The factorial-normalized sequence `a_n/n!` is strictly log-concave at every
   tested center 2–399, and has equality at center 1. The exact test is
   `(n+1)*a_n^2 > n*a_(n-1)*a_(n+1)`. All tested normalized ratios are above mu.
   This is strong finite evidence, not a proof of global log-concavity.
4. `c_n` is positive and slowly decreasing on the large-n range, rather than
   increasing as in a dominant positive `exp(A*n^sigma)` correction with
   fixed `A,sigma>0`. Its logarithmic slope is negative and moves toward zero.

| n | source | h_n | g_n | c_n |
|---:|:---|---:|---:|---:|
| 100 | exact | 22.0137088785 | 8.02620055256 | 1.48259219601 |
| 176 | exact | 26.7698812146 | 8.85014130191 | 1.44496358111 |
| 400 | exact | 34.5036804481 | 10.0154282936 | 1.40204587980 |
| 800 | long double | 41.7744627482 | 10.9771569991 | 1.37706557791 |
| 1000 | long double | 44.2569370449 | 11.2835625443 | 1.37090521173 |

The data support investigating a **lognormal-scale correction**. In particular,
the conditional ansatz

```
h_n = alpha*(log n)^2 + beta*log n + gamma
      + P_2(log n)/n + ...
```

gives alpha estimates 0.665913, 0.666559, 0.666678 on the respective intervals
100–200, 200–400, 400–800. Adding a quadratic `P_2(log n)/n^2` yields
alpha = 0.66666764 on 500–1000, with beta about 2.12357. Thus **alpha=2/3 is a
useful conjectural target**, not a proved result. Beta around 2.1236 and
exp(gamma) around 0.1008 are conditional fit observations, not established
asymptotic constants. The higher-order fits become ill-conditioned and their
small numerical residuals must not be presented as rigorous error bounds.

The logarithmic basis matters: low-degree polynomial extrapolation of c_n
in `1/log n` is unstable and does not independently determine the limit.
For n=500–1000, degrees 1,2,3 predict 1.174,1.357,1.598 respectively.

An out-of-range check is helpful. A fit on n=200–400 to
`alpha L^2+beta L+gamma+(d L+e)/n` predicts h_n through 800 with maximum error
about 3.18e-5. Three-parameter fits `A*n^sigma+B*log n+C` with sigma=0.06,
0.08,0.10 miss by about 0.023,0.028,0.033. These are diagnostics of competing
finite-range models, not exclusions of all possible subleading alternatives.

## Efficient exact recurrence

`P_n(s,u,k)` counts compacted states after n letters, starting from
`P_1(1,1,1)=1`. Its transitions are precisely the earlier report's four child
types. Reachability gives

```
0 <= s <= n,  s == n mod 2,
1 <= u <= 1+(n-s)/2,
0 <= k < s+u.
```

For a fixed source `(s,u)` put `m=s+u`,
`prefix_i = sum_(k<=i) P_n(s,u,k)`,
`suffix_i = sum_(k>i) P_n(s,u,k)`. Then, for each `0<=i<m`:

```
i<s:
  P_(n+1)(s-1,u+1,i) += prefix_i
  P_(n+1)(s-1,u,i)   += suffix_i
i>=s:
  P_(n+1)(s+1,u,i+1)   += prefix_i
  P_(n+1)(s+1,u-1,i+1) += suffix_i, when that state is valid.
```

The excluded last-state or u=1 suffixes are identically zero. Summing all
target states gives `a_(n+1)`. Prefix and suffix sums remove the per-state rank
loop: the cost is `O(N^4)` big-integer additions and `O(N^3)` stored integers.
The floating version rescales every transition by `1/((n+1)*mu)`, computes
suffixes directly without subtractive cancellation, and uses Kahan summation
for each scalar total.

## A structural identity relevant to log-concavity

Under the compacted-state distribution for uniformly sampled length-n words,
put `m=s+u` and `M_n=a_(n+1)/a_n=E[m]`. Direct summation of the four child types
gives

```
sum_children m_child = m^2 + u-k,
M_(n+1) = (E[m^2]+E[u-k])/E[m].
```

Consequently log-concavity of `a_j/j!` at center j=n+1 is equivalent to

```
(n+1)*(Var(m)+E[u-k]) <= E[m]^2.
```

This equivalence is exact; proving its inequality uniformly remains open here.

The separate `check_generic_logconcavity.py` also tests the stronger property
that `(T^j 1)(s,u,k)/j!` is log-concave in j for every starting state with
`s+u<=8`, at each center `1<=j<=15`. All 3060 tests on 204 starting states pass.
This suggests investigating an all-state preservation theorem; it supplies no
such theorem by itself. The same script checks the moment identity above.

## Reproduction and files

Needs a C++17 compiler, GMP headers/libraries, and Python with `mpmath`, `numpy`
(plus `matplotlib` for the optional plots).

```
g++ -O3 -std=c++17 exact_counts.cpp -lgmpxx -lgmp -o exact_counts
./exact_counts 400 exact-counts-400.txt 2>exact-counts-400.log
g++ -O3 -std=c++17 floating_counts.cpp -o floating_counts
./floating_counts 1000 floating-counts-1000.txt 2>floating-counts-1000.log
python analyze.py > analysis-summary.json
python fit_log_polynomials.py > log-polynomial-fits.txt
python check_generic_logconcavity.py
python plot_diagnostics.py
```

The exact and floating runs took about 62 s and 278 s respectively in the
available environment. Larger runs can require several GiB of memory.

- `analysis.json`: comparisons, exact log-concavity tests, fit comparisons,
  and source hashes
- `diagnostics.tsv`: the full h,g,c and effective-exponent diagnostic data
- `log-polynomial-fits.json`: high-precision least-squares coefficients and
  interval/basis sensitivity
- `correction-diagnostics.png/pdf`: optional plots with exact/numerical ranges
  distinguished

No claim about an asymptotic equivalent, limiting ratio, prefactor, or expansion
is proved by these computations.
