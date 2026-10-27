# Exact kernel improvements for SubexponentialSAT

**Outcome:** a review of fifteen ProveIt research packets, an adaptive integral
separator for actual crossing blocks, and exact coefficient-extraction kernels
with proved arithmetic improvements and measured local speedups.

Read **[report.pdf](report.pdf)** for the complete article and
**[report.tex](report.tex)** for its LaTeX source. The code and all exact checks
use the Python standard library. This package is not a complete SAT solver.

## Review cutoff and comparison baseline

The final reviewed repository is
[`VladimirReshetnikov/ProveIt@6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a`](https://github.com/VladimirReshetnikov/ProveIt/tree/6d3adc45061535ebe6fa7cd3d9b37dff7dcfc22a/Computability/SubexponentialSAT).
The upstream preprint pin is
[`openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`](https://github.com/openai/math/tree/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026).
The review includes the eight later packets that were initially incoming,
including the matching refinement. Source paths, Git blob identities, and
SHA-256 hashes are recorded in [provenance/source_manifest.json](provenance/source_manifest.json).

The comparison combines compatible existing ingredients before claiming a new
improvement. One explicit polynomial-space combination has normalized
contraction coefficient **66.6051**, combining asymmetric packing with
full-block Cauchy modes. A compatible construction using more memory has time
coefficient **44.5376** and space coefficient **39.4959**. These multiply
`s / sqrt(log2(s))` in base-two exponents for the report's root-network
parameter `s`; they are not measured speeds or coefficients in the SAT variable
count. They are comparison examples, not global optima. Smaller schedule
boundaries are distinguished in the article.

The strongest justified SAT order in the reviewed corpus remains

\[
\operatorname{poly}_k(n,m)\,
2^{O_k\!\left(\frac{n}{\sqrt{\log n}}
\min\{\log(2+m/n),\log\log n\}\right)}.
\]

This package does not improve that global logarithmic order. The stronger
conditional summation targets in earlier packets remain conditional.

## New local results

### 1. Use the actual crossing matrix

`code/adaptive_modes.py` separates each actual real-port crossing matrix over
the finite chain ring `(Z/2^p)[U]/f(U)`, with `f` monic and irreducible modulo
two. Minimum-valuation elimination returns exact integral rank-one modes
without requiring additional precision during separation.

If the resulting sorted Smith weights are `lambda_j`, and another integral
rank-one separation of that same matrix has sorted certified weights `w_j`,
then there are no more adaptive modes and `lambda_j >= w_j`. Consequently

\[
\#\{\beta:\textstyle\sum_j\lambda_j\beta_j<p\}
\leq
\#\{\beta:\textstyle\sum_jw_j\beta_j<p\}.
\]

One checked sparse block has **260 feasible tuples**, compared with **3,013**
for the restricted full-block basis after zero-mode removal and valuation
normalization. These are exact local inventories, not timing measurements.
Dense blocks retain the known slope-four profile. The theorem is about scalar
chain-ring crossing matrices; it is not asserted for arbitrary matrices over
nilpotent coefficient extensions.

### 2. Stream affine evaluations and pair symmetric samples

For `R` affine factors and requested exponent vector `beta`, homogenize to
`b = (R-sum(beta), beta)`. For possible targets define

\[
G=\prod_i(b_i+1),\qquad
\nu=\sum_i v_2(b_i!),\qquad
O=\sum_{b_i\text{ odd}}b_i.
\]

`code/streamed_coefficients.py` implements two replacements:

| Method | Product evaluations | Working precision |
|---|---:|---:|
| Existing finite differences | `G` | `p + nu` |
| Gray updates | `G` | `p + nu` |
| Anisotropic antipodal Gray | `floor(G/2)` | `p + nu + O - 1` |

After reading the input, Gray updates reduce the dense affine-evaluation
overhead from `O(R q G)` to `O(R G)` coefficient-ring operations, where `q`
counts positive homogenized exponents. All methods use polynomial working
space. If every exponent is even, antipodal extraction uses **one fewer
working bit** than the original routine. Squarefree targets require extra
bits, so halving samples alone is not a universal wall-clock guarantee.

The extractors support arbitrary monic `f` and nilpotent truncation
`V^ell=0`, preserve creation-time canonical representatives, and divide out
powers of two only after computing at sufficient precision.

### 3. Remove one axis with roots of unity

`code/projective_coefficients.py` implements the projective filter when every
positive homogenized exponent is one or two. It fixes an axis with smallest
positive exponent and uses roots of order `b_i+1` on the others. If `q1`
exponents equal one and `q2` equal two:

| Target profile | Product evaluations | Working precision |
|---|---:|---:|
| `q1 > 0` | `2^(q1-1) * 3^q2` | `p + q1 - 1` |
| `q1 = 0` | `3^(q2-1)` | `p` |

A cubic root must exist in the selected coefficient ring and satisfy its
relation at working precision. The quadratic ring with `f=U^2+U+1` supplies
one automatically; no ring extension is silently allocated. Degree-zero
products and impossible targets are handled separately.

## Measurements and verification

All timings compare identical deterministic synthetic inputs within each row,
using three repetitions with rotated method order and independent direct
polynomial multiplication as the correctness oracle.

| Case | Existing kernel | Improved kernel | Measured speedup |
|---|---:|---:|---:|
| Squarefree, `R=14`, scalar ring; antipodal | 1.815878 s | 0.231138 s | **7.86x** |
| Nine exponents two, scalar ring; antipodal | 2.371582 s | 0.407105 s | **5.83x** |
| Nine exponents two, quadratic ring; projective | 2.914805 s | 0.422439 s | **6.90x** |
| Six exponents two, nilpotent extension; projective | 0.080007 s | 0.017121 s | **4.67x** |

The nineteen-case antipodal suite ranges from **2.16x to 7.86x**. In the
nine-exponent quadratic case, projective extraction reduces **19,683 to
6,561 evaluations** and **41 to 32 working bits**. Projective and antipodal
methods are roughly tied on several mixed profiles; the smallest projective
case is slightly slower than antipodal. Retain both implementations.

These are packet coefficient-kernel measurements, not SAT solve times or
results on industrial SAT instances. The package contains no proof-assistant
certificate for the complete upstream ETH argument. Smith forms, Gray codes,
polarization, and roots-of-unity filters are classical; the scoped contribution
is their integration, exact precision accounting, executable checks, and
improvement beyond the inspected repository snapshot.

Recorded checks include 1,392 exhaustive scalar extraction cases, 900 random
ring cases, 10,028 exhaustive projective cases, 813 random projective
comparisons, 720 random adaptive matrices with 6,840 independent minors, and
720 actual crossing matrices. Additional independent reviews check antipodal
orbits, creation-precision invariance, and a rational Cauchy-kernel fixture.
The packaged exact suites passed in normal Python and with `-O`.

Instrumentation detail: the projective `ring_multiplications` diagnostic
excludes the single multiplication used to validate the cubic root. Exact
results, evaluation counts, and wall-clock measurements include the full
method and are unaffected.

## Reproduce

Run commands from this directory. Python **3.10 or newer** suffices for all
algorithms, verification, and benchmarks. No network access is required.

```bash
# Verify the delivered artifact hashes before making local changes:
python3 code/verify_manifest.py

# All exact suites, both normal and optimized; no benchmarks:
python3 code/run_checks.py --output results/recheck

# Optional fresh timings; preserve the originally recorded measurements:
python3 code/verify_and_benchmark.py --repeats 3 --output results/new_benchmarks
python3 code/benchmark_projective.py --repetitions 3 --output results/new_projective

# Numerical comparison certificates, separate from the exact checks:
python3 code/check_certificates.py --output results/new_certificates.json
```

`make integrity` checks the delivered artifact hashes; `make verify` runs the
exact suites. The artifact manifest excludes itself, build scratch, and caches.
`make figures` regenerates tables and
the runtime figure from the recorded JSON and requires **matplotlib**.
`make pdf` compiles the supplied article using **latexmk**, **pdfLaTeX**, and
the standard packages listed in `report.tex`; it uses the included figures
and tables. A typical TeX Live installation needs LaTeX recommended/extra,
recommended fonts, and Latin Modern. `make clean` removes only build scratch
and Python caches, preserving the report PDF and recorded results.

## Directory map

| Path | Contents |
|---|---|
| `report.tex`, `report.pdf` | Complete article and compiled PDF |
| `code/` | Exact kernels, retained baseline, verification, benchmarks, exhibit builder |
| `results/` | Raw measurements, CSV summaries, exact verification, composed constants |
| `results/release_checks/` | Checks executed from the staged release in both Python modes |
| `figures/` | Report figure as PDF and PNG |
| `notes/` | Derivations, baseline audit, independent mathematical/code reviews |
| `provenance/source_manifest.json` | Reviewed source identities and hashes |
| `provenance/artifact_manifest.json` | Delivered artifact hashes for integrity checks |
| `LICENSE` | MIT-0 license and retained-baseline attribution |

The supplied baseline is unchanged from ProveIt. Upstream manuscripts are
referenced and hashed, not redistributed as part of this package.
