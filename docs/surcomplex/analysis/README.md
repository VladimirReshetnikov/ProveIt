# Surcomplex analysis: holomorphic functions on K = No[i]

[The maintained article](article.pdf) develops local power-series calculus,
coherent Hahn sections over ordinary complex domains, contour and residue
formulas, zero clusters, and rigidity under changes of scale.
[The TeX source](article.tex) is the mathematical reference; the shared
[notation guide](../../NOTATION.md) explains its conventions relative to the
other reports.

The article was assembled from nine manuscripts dated 21 September 2026.
[`MERGE_NOTES.md`](MERGE_NOTES.md) preserves the original reconciliation and
provenance. It is a historical record: several of its comparisons are corrected
in the maintained article and described below. Original manuscripts are available
in repository history, rather than in a current `sources/` directory.

## Function classes and domains

A **germ-analytic function** is locally the Hahn sum of a power series with
surcomplex coefficients. Every formal series has a sufficiently small realization,
with a scale depending on that series. Its germ algebra is `K[[X]]`; evaluation
at one fixed point is not injective on all formal series.

A **coherent section** in `H(U)` has one well-ordered Hahn support and ordinary
holomorphic coefficient functions on one common connected ordinary domain `U`.
Its evaluation lives on the halo `U^# = st⁻¹(U)`, a class of finite elements.
A **canonical lift** `f^#` has just its ordinary coefficient at exponent zero.
The inclusions from lifts to coherent sections to germ-analytic functions are
strict. Germ-analytic functions are fine-differentiable; this article does not
establish strictness of that last inclusion or a converse regularity theorem.

Local identity, inverse, ramification, and primitive results hold for analytic
germs. Coherence supplies the propagation across the ordinary base used by the
global identity and maximum principles, open mapping, and uniqueness of coherent
primitives. Sharp Schwarz–Pick inequalities hold for canonical lifts; the coherent
self-map `(1+t)z` of the disk halo shows why they need not hold for general sections.
The multivariable implicit theorem proved here is a **germ** theorem; the coherent
inverse theorem is one-dimensional.

The full fine topology uses every positive surreal radius. Every set-sized
subset of `K` is closed and discrete, and every convergent set-indexed net is
eventually equal to its limit. This differs from the intrinsic valuation topology
of a fixed Hahn field: the partial sums of `Σ tⁿ = (1−t)⁻¹` converge intrinsically
in `ℂ((t^ℚ))`, but do not converge in the full fine topology. Ordinary integrals
and convergent series of complex coefficient functions are computed in `ℂ`
before their values enter a Hahn sum.

## Bounds, residues, and global functions

For coherent sections on the finite plane, a single surreal bound always exists.
An ordinary-real bound holds exactly for `F = c + R`, with `c ∈ ℂ` and `R` of
positive support. Coefficientwise boundedness forces a constant in `K`.
The latter two hypotheses are **incomparable**: `tZ` has real-bounded values but
unbounded coefficient functions; the constant `ω` has bounded coefficient
functions but no ordinary-real bound on its values. The coefficientwise Cauchy
majorant supplies one possible pointwise bound for the ML inequality; it also
retains coefficient data that a scalar bound alone does not recover.

The article distinguishes a formal Laurent residue, an actual local residue at a
surcomplex point, and a coefficientwise **cluster residue** at an ordinary centre.
For `1/(ζ−ε)`, with nonzero infinitesimal `ε`, the cluster residue at 0 is 1,
whereas the actual residue at 0 is 0 and the actual residue at `ε` is 1.
Uniformly bounded coefficient pole orders suffice for agreement at the centre;
they are not necessary for accidental numerical equality.

Coherent preparation gives finite zero clusters. Rouché's real-margin version
requires one ordinary `q < 1`: a bare strict surreal boundary inequality is
insufficient. On the ordinary unit circle, `F=Z` and `G=Z−1+t` satisfy
`|G−F|<|F|`, yet have respectively one and zero zeros in the disk halo; the root
`1−t` belongs to a boundary monad omitted by the halo.

The global logarithm and principal cut-plane logarithm are different fine-analytic
functions. Their values differ by `2πi` just below an ordinary negative real
point; the principal branch is continuous on its own domain. The canonical
exponential and its explicit twists have different, generally non-nested kernels.
Nevertheless `E_λ(1/z)` takes every nonzero value in every punctured fine
neighborhood of zero for each twist: the periods `iω^α`, for ordinals `α ≥ 2`,
provide the same reciprocal-period argument. This is a result about the specified
family, not a general Picard theorem.

Requiring coherent charts at **every** positive surreal scale forces global
functions to be polynomials, or rational functions in the meromorphic version.
Supports may vary with the scale; no one common support across scales is assumed.

[gamma-and-zeta-functions](../gamma-and-zeta-functions/) applies the
finite-lift zero theorem (`c:p4:liftzeros`) to Gamma, zeta and xi
(`gz:thm:divisor`), and uses the twisted exponentials of `e:thm-twisted` for its
left zeta prescription and movable zeros (`gz:prop:moving`).

## Maintained review and historical evidence

The September 2026 review read the main arguments in their logical order and
corrected the comparisons above. It also repaired the uniform Taylor-remainder
bound, justified multivariable germ faithfulness by rational directions, included
the full reciprocal support in rescaling, and extended the elementary root lemma
from infinitesimal coefficients to finite coefficients where global preparation
uses it. The geometric expansion at an undisplaced point requires
`ζ/ε` infinitesimal; merely `|ζ| < |ε|` is insufficient for strong summation.

The unchanged merge record contains older claims of three strict function-class
inclusions, a linear boundedness hierarchy, and an if-and-only-if pole-order
criterion. Read the maintained statements in their place. Historical `code/`,
`data/`, and `MERGE_NOTES.md` are preserved as supplied; finite verification is
not a proof of the general support, topology, or class-size arguments.

Two imported scopes were checked directly against primary texts:
[Ehrlich–Kaplan, arXiv:2002.07739v3](https://arxiv.org/pdf/2002.07739v3),
Proposition 11.2 and Theorem 11.1, pp. 33–34, for the canonical exponential and
kernel; and [Poonen, *Maximally complete fields*](https://math.mit.edu/~poonen/papers/amsval.pdf),
Corollary 4 on PDF p. 10, for algebraic closedness of a Hahn field with divisible
value group and algebraically closed residue field. These checks do not constitute
an exhaustive literature or priority review.

## Files and reproduction

- `article.tex`, `article.pdf`: maintained exposition and compiled article.
- `MERGE_NOTES.md`: historical source reconciliation.
- `code/`: nine preserved finite verification programs.
- `data/`: historical run outputs.

The review reran all nine programs successfully on temporary copies using Python
3.13.14 and SymPy 1.14.0. They check finite coefficients, residuals, and residue
identities, rather than the full theorems. From this directory, rerun without
writing into the historical evidence directories:

```sh
analysis_check_dir=$(mktemp -d)
cp -R code "$analysis_check_dir/code"
for script in "$analysis_check_dir"/code/*.py; do
  uv run --with sympy==1.14.0 python "$script" > "$script.log"
done
```

Build the PDF with three `pdflatex` passes in a temporary output directory:

```sh
analysis_build_dir=$(mktemp -d)
for pass in 1 2 3; do
  pdflatex -interaction=nonstopmode -halt-on-error \
    -output-directory="$analysis_build_dir" article.tex
done
```

The maintained PDF has 96 pages. Its three-pass build has no errors, unresolved
references, package warnings or overfull boxes; eight underfull-box notices
remain. The revised theorem passages were inspected.

These are AI-assisted research notes. The review and finite checks do not amount
to external refereeing or a complete machine-checked formalization.
