# Verification of the Lambert inverse late-coefficient formulas

The delivered run passed **5,890 exact assertions** and evaluated **70 main
numerical cases**, including complete finite coefficient sums through
`n = 1025`. The high-precision comparisons, generated tables, and plots are
recorded in this directory. No parameters were fitted to numerical data.

The article's proofs establish the infinite asymptotic and analytic statements.
These files check finite algebra, the numerical implementation, and the observed
error scales. **Floating-point results are not interval certificates.**

## Mathematical normalization

The forward formal coefficients and inverse equation are

\[
r_n=\frac{(-1)^n}{n!}\zeta(1-n)^2,\qquad
R(q)=\sum_{n\ge1}r_nq^n,\qquad
V+\frac u2V^2+uR(qe^{-V})=0,
\]

with `V(q,u) = sum C_n(u) q^n`. In particular, `R` includes the linear
coefficient `r_1 = -1/4`. Define

\[
A=4\pi^2,\qquad c=A/4=\pi^2,\qquad
b_n=\Gamma(n)/n,\qquad d=A^2/288,
\]

and normalize the computed coefficient as

\[
Z_n(u)=\frac{(-1)^{n+1}A^nC_n(u)}{4u b_n}.
\]

Let `epsilon = n mod 2`, `z = c u`, and put

\[
H_0(z)=\cosh z,\qquad H_1(z)=\sinh z,
\]

\[
K_\epsilon(u)=
\left(\frac{(1+u)z^2}{2}+du\right)H_\epsilon(z)
+(2+u)zH_\epsilon'(z).
\]

The numerical comparison is with

\[
Z_n(u)=H_\epsilon(cu)+K_\epsilon(u)/n+O(n^{-2}).
\]

The full first-correction coefficient is consistently named **`K`** in the
plots and **`K_first_correction`** in the JSON and CSV files. It is not the
separate polynomial named `P(u)` elsewhere in the article.

## Exact finite checks

The script constructs `C_1,...,C_12` over the exact polynomial ring `Q[u]`
in two ways. One uses the finite Lagrange formula. The other recursively solves
the original implicit equation, using the differential recurrence for
`exp(-m V)` to determine each next coefficient from the preceding ones.
The second construction does not use the Lagrange coefficients as input.
The result is also substituted directly into the implicit equation.

| Category | Recorded checks |
|---|---:|
| Equality of the independent coefficient constructions, `n = 1,...,12` | 12 |
| Degree, valuation, signs, Catalan top coefficient, and exact lowest coefficients | 65 |
| Vanishing substitution residual at `q^0,...,q^12` | 13 |
| Two-factor inequality `sum b_j b_(n-j) <= 3 b_(n-1)`, through `n = 100` | 99 |
| Interior inequality `sum_(j=2)^(n-2) b_j b_(n-j) <= 6 b_(n-2)`, through `n = 100` | 97 |
| Rational gamma-ratio consequence for every `1 <= k <= n <= 100` | 5,050 |
| Convolution-power inequality for every `1 <= k <= n <= 32` | 528 |
| First-correction endpoint and inner-factor algebra, and both hyperbolic parity sums | 26 |
| **Total** | **5,890** |

The exact gamma-ratio tests use

\[
\frac{n^{k-1}b_{n-k+1}}{b_n}\le k\,3^k,
\]

including `k = n`. This is a rational consequence of the sharper bound
`k exp(k)` proved analytically in the article. The finite script does not
mislabel a floating-point comparison with `exp(k)` as an exact rational test.

`coefficients_exact.txt` contains all twelve complete polynomials.
`exact_results.json` records their degrees, valuations, and the tested ranges.

## Complete main coefficient sums

The numerical calculation first makes the forward coefficients nonnegative:

\[
a_n=A^n(-1)^nr_n,\qquad a_1=c,\qquad
a_{2j}=4b_{2j}\zeta(2j)^2,\qquad a_{2j+1}=0\quad(j\ge1).
\]

For `S_(n,k) = [z^n] a(z)^k`, it computes
`F_(k,l) = S_(k+l,k)/b_(l+1)` with a triangular recurrence. The matrix weights
are

\[
\frac{a_{\ell-m+1}}{b_{\ell-m+1}}
\frac{\ell+1}{(m+1)(\ell-m+1)\binom{\ell}{m}},
\qquad 0\le m\le\ell.
\]

This removes the large factorial scale before convolution. The finite
Lagrange formula is then evaluated with its gamma ratio normalized in the
same way. Compensated summation is used for the final coefficient sum.

**Every term `1 <= k <= n` is included in each main coefficient value.**
There is no mathematical truncation of the finite coefficient sum in the main
table. Ordinary floating-point rounding is still present and is documented
below. The coefficient calculation does not use the leading or first-correction
asymptotic formulas to generate its values.

The recorded main grid is the Cartesian product of these ten indices and seven
parameter choices:

- `n = 64, 65, 128, 129, 256, 257, 512, 513, 1024, 1025`;
- `u = 0.01, 0.05, 0.1, 0.2, 0.5`;
- complex `u = 0.1 + 0.05 i`;
- moving `u = 1/log(n + e)`.

Adjacent even and odd indices test both hyperbolic amplitudes. The moving
parameter tests the small-parameter regime covered by the uniform theorem.

## Exact meanings of the numerical error fields

For `H = H_epsilon(cu)` and `K = K_epsilon(u)`, the JSON and CSV store the
signed, possibly complex quantities

\[
e_0=\frac{Z_n-H}{H},\qquad
e_1=\frac{Z_n-H-K/n}{H},
\]

as `relative_leading_error` and `relative_first_corrected_error`, respectively.
Their denominator is **the leading amplitude `H`**, not the computed value
`Z_n` and not `H + K/n`. The files also store `n e_0` and `n^2 e_1`.
Complex fields have separate real and imaginary components.

The top panels of `asymptotic_errors.pdf` show `|e_0|` as dashed curves and
`|e_1|` as solid curves. The bottom panels show the signed real value `n^2 e_1`.
The plots use the positive real parameters `u = 0.05, 0.1, 0.2` and both
parities. The complete grid, including the complex and moving parameters,
remains in `diagnostics.csv` and `results.json`.

At the largest even and odd indices, adding the independently derived first
correction reduced the recorded error by factors between approximately
**37 and 592**. These are diagnostics of agreement with the theorem, not a
numerical proof of the theorem.

## Independent precision checks

### High-precision recalculation

An independent mpmath calculation uses **80 decimal digits**, recomputes the
normalized convolution weights from exact integer binomial coefficients, and
includes every `k <= n`. It checks the indices
`6, 7, 12, 64, 65, 128, 129` with five parameter choices:
`u = 0.01, 0.1, 0.5`, the complex parameter, and the moving parameter.
This gives **35 precision comparisons**.

The comparison metric is

\[
\frac{|Z_n^{\mathrm{extended}}-Z_n^{\mathrm{mpmath}}|}
     {\max(1,|Z_n^{\mathrm{mpmath}}|)}.
\]

It is a relative-or-absolute error, not an interval enclosure. Its recorded
maximum is `2.35690922554003295e-19`. At indices `6, 7, 12`, direct evaluation
of the exact rational polynomials supplies another **15 comparisons** with
the high-precision normalized formula; their maximum error is
`4.6764021837458509e-81` in the same type of normalization.

### Secondary large-index precision comparison

A separate calculation uses binary64 convolution weights and arithmetic at
`n = 512, 513, 1024, 1025`, followed by extended-precision evaluation of the
finite sum. It checks all seven parameter choices, giving **28 comparisons**.
Its largest recorded relative-or-absolute difference from the complete main
calculation is `3.11012993116789592e-16`.

This secondary calculation stops at `k = 256`. For `|u| <= 1/2`, the article's
bounds, with coefficient-majorant constant `12` and `e < 3`, bound the normalized absolute contribution
of the `k`th term to `D_n/(4b_n)`, where
`D_n = (-1)^(n+1) A^n C_n`, by `k 81^k/(18 k!)`. Hence the omitted terms
have the exact rational upper bound

\[
\frac{81^{257}}{18\,256!}
\frac{1}{1-81/257}
=2.86024187744886758\ldots\times10^{-18}.
\]

The exact numerator and denominator are recorded in `results.json`. Divide
this bound by `|u|` to obtain the corresponding bound for `Z_n`. The bound
controls **omitted terms only**; it does not certify the floating-point
rounding error. The complete main table does not require this truncation
bound.

## Replay and recorded environment

From the package root, install the pinned dependencies and run:

```bash
python -m pip install -r verification/requirements.txt
python verification/verify.py --output-dir replay-verification
```

The separate output directory preserves the delivered evidence. Running
without `--output-dir` regenerates the result files in `verification/`.
The default options are `--max-index 1024 --exact-order 12 --dps 80`.
The index option selects the listed even base indices up to that bound and
includes each adjacent odd index; therefore the default includes `n = 1025`.
A smaller replay can use `--max-index 128`; its result records identify the
reduced grid. Verification needs no network access once the dependencies
are installed.

| Component | Recorded version or property |
|---|---|
| Python | 3.12.14 |
| Operating environment | Linux x86_64, glibc 2.39 |
| NumPy | 2.3.5 |
| mpmath | 1.3.0 |
| SymPy | 1.14.0 |
| Matplotlib | 3.10.8 |
| Main long-double significand | 64 bits |
| Main long-double maximum binary exponent | 16,384 |
| Independent mpmath precision | 80 decimal digits |

The main implementation requires an extended-range `numpy.longdouble` with
at least a 64-bit significand and the exponent range checked by the script.
On platforms where `longdouble` aliases ordinary binary64, including common
Windows configurations, the script **stops explicitly**. It does not silently
lower precision or claim an untested fallback. The supplied run was made in
the Linux environment above. Its elapsed time is recorded in `run.txt`;
runtime can vary even though the mathematical inputs and calculations are
deterministic.

## File map and evidence limits

| File | Contents |
|---|---|
| `verify.py` | Complete deterministic verification and plotting program |
| `requirements.txt` | Exact dependency versions used for the recorded run |
| `exact_results.json` | Exact identities, coefficient records, and finite test ranges |
| `coefficients_exact.txt` | All coefficient polynomials through `C_12(u)` |
| `results.json` | Full metadata, all main diagnostics, precision comparisons, exact tail certificate |
| `diagnostics.csv` | Flattened main grid, normalized values, and real/imaginary error components |
| `run.txt` | Successful-run summary and elapsed time |
| `asymptotic_errors.pdf` | Vector publication figure used by the article |
| `asymptotic_errors.png` | Raster preview of the same figure |

The exact identities and rational inequalities are finite symbolic checks.
The exact secondary tail certificate is a mathematical bound on an omitted
sum. The numerical coefficient values and precision comparisons use ordinary
floating arithmetic. None of these finite checks substitutes for the uniform
convolution proof, the infinite large-order theorem, analytic continuation,
or the Stokes-transport proof in the article. No proof-assistant compilation,
interval certification, or external peer review is claimed.
