# Independent exact-coefficient verification and numerical diagnostics

These computations concern fixed L-convex polyominoes, OEIS A126764. Rotations
and reflections are not identified. The current OEIS entry explicitly labels
the sequence "fixed" and points to A360055 for the free case.

## Sources and provenance

- OEIS entry: https://oeis.org/A126764
- Published integer table: https://oeis.org/A126764/b126764.txt, all n=0,...,2000
- Guttmann and Kotesovec, arXiv:2109.09928v3:
  https://arxiv.org/html/2109.09928v3, equations (3), (4), and (5)

The integer table was read on 2026-10-02 in overlapping source windows.
All 2001 distinct index/value pairs were collected. `b126764_web.txt` is the
normalized snapshot (one decimal index, one space, one decimal value, newline),
not a claim to reproduce original HTTP bytes. Its SHA256 is

`d036795c5c67b45836e4dbd76036ef0af520baf4751aaf88421f853e5cedf027`.

## Exact arithmetic

The original source has f_0=1, f_1=1+2q-q^2 and
f_k=2 f_(k-1)-(1-q^k)^2 f_(k-2). It gives

A(q)=1+sum_(k>=0) q^(k+1) f_k /
  [(1-q)^2 ... (1-q^k)^2 (1-q^(k+1))].

The faster exact implementation sets b_(-1)=b_0=1,
b_k=(2 b_(k-1)-b_(k-2))/(1-q^k)^2, and
A(q)=1+sum_(k>=1)(q^k-q^(2k))b_k.
Equivalently b_k=f_(k-1)/(q;q)_k^2 for k>=1.
Each division by 1-q^k is performed by an integer geometric-prefix pass.
Degree N truncation is exact and takes O(N^2) integer operations.

Results:

- All 2001 OEIS terms n=0,...,2000 agree exactly
- Independent literal evaluation of the original f-sum agrees through n=400
  (every original denominator is applied afresh, without the b-transform)
- Exact coefficients were extended to n=8000 in about 15 seconds
- Terms n=2001,...,8000 are newly generated here, not compared to published data
- Tests use explicit exceptions, not assert; ordinary Python and python -O pass

## Reproduction

Dependencies: Python 3, mpmath, SymPy. Run in this directory:

```
python verify_exact.py --max-n 8000 --literal-n 400 --output verification_results_8000.json
python -O verify_exact.py --max-n 8000 --literal-n 400 --output verification_results_8000_optimized.json
python check_diagnostics.py --max-n 8000 --output diagnostics_8000.json
python -O check_diagnostics.py --max-n 8000 --output diagnostics_8000_optimized.json
python scan_lambert_rounding.py --max-n 8000
```

`symbolic_results.json` is a copy of the independently derived coefficient and
inverse polynomials. `check_diagnostics.py` also recomputes the coefficients
from the half-integer Bessel polynomial formula and checks agreement at 100
decimal digits. See `../symbolic/check_inverse.py`
for exact Gaussian-saddle and formal-reversion verification.

## Selected diagnostics (not proofs)

Put K=13*pi^2/24, delta=13*sqrt(2)/768, z=2*sqrt(K*n).
The analytic prediction is delta*n^(-3/2)*exp(z)*sum_(r>=0)b_r/z^r.

| n | exact/leading | relative prediction error through z^-4 | through z^-8 |
|---:|---:|---:|---:|
| 2000 | 0.976025253412435921 | -1.443558234e-6 | -1.184484504e-9 |
| 4000 | 0.983206124724057642 | -2.623793126e-7 | -5.493323047e-11 |
| 8000 | 0.988210257959352301 | -4.735525978e-8 | -2.517837511e-12 |

Let A=delta*(2*sqrt(K))^3 and
z_0(y)=-3 W_(-1)(-(A/y)^(1/3)/3), n_0(y)=z_0(y)^2/(4K).
Observed n-n_0(a_n) is 0.47624742230330, 0.46806132666914,
0.46212708952736 at n=2000,4000,8000. The analytically predicted limit is
36/(13*pi^2)+1/6=0.447248405983909726....
At n=8000, the fourth-order Lambert-corrected index error is -1.4465398e-6;
the logarithmic inverse through Y^-3 has index error -7.800905079e-6.

A 70-digit finite scan finds rounding n_0(a_n) to the nearest integer correct
for every n=556,...,8000 and incorrect for n=2,...,555; n=1 has no real branch.
This is an observed finite range, not a proof of an exact onset or eventual
validity. At n=556 the uncorrected bias is 0.4999926552499488256.

## Source inconsistency

Equation (5) of arXiv v3 and the current OEIS conjecture give amplitude delta.
The final display of Section 2 in v3 has its reciprocal, while that section's
quoted decimal constant is delta. The numerical evidence agrees with delta.
The article's c versus 1/c notation around equation (22) is also inconsistent;
use the explicit amplitude in equation (5), not the final Section 2 display.
