# Additional mathematical review and verification notes

These are additional independent derivation and implementation checks
performed **within this research session** on 10 October 2026. They are
not external peer review, and no formal proof assistant was used. Their
purpose is to check the proofs, conventions, and computational
normalizations by a separate derivation or calculation. The general
analytic proofs remain those in the article; finite numerical agreement
does not certify them or establish historical novelty.

## Formula map

| Research-draft formula | Article label | Content |
|---|---|---|
| D13 | `dg:closed` (display `dg:closedeq`) | Closed evaluation at every nonpositive-integer Dougall resonance |
| D15 | `dg:alljets` (display `dg:alljetseq`) | All resonant Stieltjes Taylor coefficients |
| D35 | `dg:quarticN1jet` | Explicit quartic first harmonic jet at the next resonance |

## Independent algebra checks

The three mapped formulas were rederived. The Dougall prefactor reduces
to `(a/2) Gamma(a)/Gamma(1+a) = 1/2`; this agrees with the half residue
of the colliding Hurwitz factor. The coefficient differential law
includes the motion of the center `eta=a/2`. At an integer resonance it
cancels the shifted digammas and gives `dg:closed`, with a regular final
expression even at zeros of the residue polynomial.

For `dg:alljets`, direct Laurent coefficient extraction confirmed the
ordinary Taylor factorials, the terms `e_(m+1)/2` and `c_(N,m+1)/2`, and
the Stieltjes factors `(-2)^h gamma_h(eta)/h!`.

For the explicit first harmonic jet, the independent expansion was

```text
E_1(t) = E_0(t) (1/2-t)^3/(t-1),
(1/2-t)^3/(t-1) = -1/8 + 5t/8 - 7t^2/8 + O(t^3),
E_0(t) = 1 + 2g3 t + (2g3^2-zeta(2))t^2 + O(t^3),
g3 = EulerGamma + 3 log 2.
```

It reproduces every coefficient of `dg:quarticN1jet`. The moving-zero
head was also checked: the `n=0` first Taylor coefficient is `pi^2/8`
and remains in the summed identity.

## Completed independent cutoff calculation

The nonlinear correction was checked through a source-coordinate
primitive calculation, independently of its proposed residue formula.
For `g=f^{-1}`, the calculation transforms each test jet to
`(phi o g) g'`, integrates the singular powers and logarithms in the
source coordinate, composes the resulting primitive with `f`, and
extracts its lower-cutoff constant. Including the inverse Jacobian
tests the article's scalar-distribution pullback convention.

The completed exact comparison used

```text
f(t) = q [t + (2/3)t^2 - (1/5)t^3 + (1/7)t^4],  q = 1 or 2,
r = 0,1,2,3,   n = 0,...,2r+2,
phi(t) = 1,t,...,t^r near zero.
```

All **48 coordinate/index cases and 140 monomial pairings passed**.
The nonunit-scale cases retain exact powers of `log 2`. This check is
included in `code/verify_nonlinear.py` through
`code/independent_cutoff.py`; its completed evidence is the
`independent_cutoff` entry in `results/nonlinear_checks.json`.

The cocycle was separately checked with its required transformed input,
`A_(g o f)[h] = f^* A_g[h] + A_f[h o g]`. The lowest logarithmic power
also independently gives the sharp maximum delta order
`min(r-1,2r-n-1)`, vanishing for `n>=2r`, and the stated leading
coefficient. Comparisons involving distributional derivatives use the
article's now-explicit common smooth periodic completion of the analytic
remainder; this prevents unintended step-function contact terms.

## Previously completed raw harmonic sum

A separate calculation used **50 decimal digits** and no asymptotic
tail completion. It updated only the elementary quantities

```text
w_(n+1)/w_n = (n+5/4)/(n+1/4) [(n+1/2)/(n+1)]^4,
H_(2n+2) = H_(2n) + 1/(2n+1) + 1/(2n+2),
w_0 = pi^2/4,  H_0 = 0.
```

For `dg:quarticN1jet`, the right side evaluated to

```text
-0.01478077433551891370099138776585423743252.
```

The exact previously recorded decimal output is:

| Summands | Raw partial sum | Partial sum minus right side |
|---:|---:|---:|
| 100 | -0.0147713680976139935242147586194 | 9.40623790492e-6 |
| 1,000 | -0.0147806446612861215607874822991 | 1.29674232792e-7 |
| 10,000 | -0.0147807726795274702910003643217 | 1.65599144341e-9 |
| 30,000 | -0.0147807741324522597954916761851 | 2.03066653905e-10 |

These are observed discrepancies, not rigorous tail bounds. The
reproduction script is independent of the asymptotic-tail verifier:

```bash
python code/verify_dougall_direct.py
```

It writes `results/dougall_direct_checks.json` when run. The packaged
script was syntax-checked during final assembly; the already completed
30,000-term calculation was not rerun at that step. This additional
diagnostic is deliberately separate from the three-script default
runner.

## Final review of the transport and correlation sections

The final mathematical reading of `sections/05_transport.tex` and
`sections/06_correlations.tex` found **no substantive proof gap or
incorrect coefficient**. The review checked:

- The full disjoint-grid hypotheses and their gcd characterization.
- Stieltjes multiplication, its ambient-coordinate mean, all triple
  scale corrections, and the signs of the pair and constant terms.
- The pair generator, its removable denominators, and
  `J_00(c)=gamma_1(c)+gamma_1(1-c)-2 zeta(2)`.
- The triple coefficient exponents and factorials, the weighted root
  filter, and joint entire continuation for nontrivial colors.
- The Mellin formula for the derivative normal to `C=-N`, including
  the term `-psi(N+1) f_N` and the denominators `j-N`.
- The centered Gamma correlation's sign and factor `-1/(4 pi^3)`;
  the unit digamma formula; and every coefficient of the explicit
  twelfth-root example's lower polynomial.

Two small wording issues raised in that final reading are **resolved**
in the supplied article: the unit digamma quantity explicitly requires
pairwise distinct shifts modulo one, and the Gamma differentiation
proof specifies the uniform majorant
`t^(-rho)(1+|log t|^3)`, with `0<rho<1`, near the spectral point.
The global positive-real-part spectral identities retain their stated
disjoint-grid hypotheses throughout.
