# Cauchy's integral theorem and the residue theorem in iPRA

This package contains a complete human-readable argument for explicit,
quantitative constructive versions of Cauchy's integral theorem and the residue
theorem, together with exact-arithmetic reference code and a concrete Lean
formalization plan.

Start with **report.pdf**. Its standalone source is **report.tex**.

## The precise result

The mathematical theorems are schemas in fixed primitive-recursive rational
approximation procedures. The inputs include uniform continuity and uniform
first-order differentiability moduli, magnitude bounds, positive separation
bounds, and finite geometric data. First-order iPRA is not treated as a theory
with variables for arbitrary real functions or sets.

For a rational oriented triangle of taxicab diameter D and perimeter P, the
central finite estimate is

    norm(T_(m,n)(boundary triangle))
      <= D*P*2^(-k) + P*2^(-n)*(2^(m+1)+D),

provided D*2^(-m) <= 2^(-mu(k)). It is proved by processing all 4^m midpoint
subtriangles, annihilating their affine parts exactly, and cancelling shared
edges. The second term includes the growing total internal perimeter; the
sample-precision schedule explicitly compensates for that factor.

This yields Cauchy's theorem for finite filling chains. A separate rational
calculation proves the square moments of all integer powers, including

    integral_boundary_Q (z-a)^(-1) dz = 2*pi*i.

The proof then **derives Laurent coefficients and a uniform tail** from an
annular Cauchy formula; a Laurent expansion is not assumed. With s=r/8, R=8r,
the approximation on the middle square is

    norm(f(z) - sum(k=-N,...,N-1) a_k*(z-a)^k) <= C_r*2^(-N),
    C_r = 16*R*M_R/(R-r) + 16*s*M_s/(r-s).

Rational planar fillings give

    integral_Gamma f(z) dz = 2*pi*i*sum_j winding(Gamma,a_j)*Res(f,a_j).

The coefficients are unique Laurent coefficients, and the indices agree both
with finite ray-crossing counts and the normalized kernel integrals. Isolated
essential singularities are included; no finite pole order is required.

## General curves

The paper also proves a controlled extension to PR-presented uniformly
continuous rectifiable curves with a supplied variation bound. It gives a
rational Stieltjes integral name, quantitative polygon approximation, and
homotopy invariance from a grid of 2*4^m rational triangles. Intermediate
homotopy paths need not be rectifiable.

The extension requires a PR homotopy modulus and a positive analytic collar.
For residues, a sufficiently close rational polygon must have the stated
global filling certificate. The core residue theorem uses rational singularity
centres. Arbitrary classical holomorphic functions, unspecified qualitative
moduli, arbitrary real singularity locations, and bare topological simple
connectedness are not silently promoted to these effective inputs.

## Logical accounting

All analytic equalities abbreviate explicitly controlled rational inequalities.
Precision is fixed before induction; finite conjunctions use PR Boolean folds;
induction invariants concern rational sums, signed edge multiplicities, or
bounded computation checks. There is no universal PR evaluator for arbitrary
PR program codes, no compactness step, and no induction on an analytic formula.

The proof reuses the inspected ConciseIPRA foundation and is consistent with the
name and finite-telescoping conventions in the inspected calculus draft. All
analytic arguments needed here are included in the manuscript.

## Formalization status

**The Lean source is an uncompiled candidate, not a completed formalization.**
No Lean, Lake, or Elan executable was available in the authoring environment.

`lean/FiniteCore.lean` contains nine proposed proof scripts for elementary ring
identities. It has no admitted proof terms or new axioms, but its scripts have
not been checked by Lean. Its four-triangle cancellation concludes equality
with the refined six-edge boundary, as required for arbitrary sample values.

`lean/ROADMAP.md` states the actual remaining goal: construct deeply embedded
derivations `Gamma ⊢[PRAAx] phi`, then use the existing `pra_iff_native` bridge.
An ordinary Lean theorem about `Rat` or `Complex` would not meet that goal.
The roadmap covers PR encodings, finite arithmetic contracts, QF invariants,
integration names, square moments, Laurent coefficients, topology, residues,
effective curves, and kernel-checking criteria.

## Files

| File | Purpose |
| --- | --- |
| `report.tex`, `report.pdf` | Complete mathematical manuscript and compiled PDF |
| `lean/FiniteCore.lean` | Uncompiled proposed finite algebra proofs |
| `lean/ROADMAP.md` | Detailed path to embedded iPRA proofs |
| `code/rational_contours.py` | Exact rational complex arithmetic, quadrature, subdivision, grid filling, and pi |
| `code/test_rational_contours.py` | Seven finite validation tests |
| `code/run_validation.py` | Reproduces tests and the numerical example |
| `code/validation_results.json` | Exact fractions, error bounds, and display values |
| `provenance/sources.json` | Pinned source URLs, hashes, and inspection scope |
| `provenance/build_validation.json` | PDF, code, and formalization status |
| `Makefile` | PDF build and finite-validation commands |
| `SHA256SUMS` | SHA-256 hashes of the delivered files |

## Reproduce the checks

Python 3.10 or later and the standard library suffice:

```sh
python3 code/run_validation.py
```

The runner executes seven tests and rewrites the validation JSON. The tests
and all mathematical comparisons use exact `fractions.Fraction` arithmetic.
Floating-point entries are displays only.

The sample integrand is `1/z+2/(z-1)` on the rectangle
`[-2,3] x [-2,2]`. A grid of 26 triangles fills the rectangle minus squares of
half-side 1/4 at its poles. The boundary certificate is verified exactly. At
depth 9 with 32-bit sample evaluation, the outer contour sum has imaginary
part approximately 18.849555246653495 and certified error below 0.000083690,
consistent with the proved value 6*pi*i. The paper explains how smaller local
Laurent squares connect to these larger numerical holes by square-annulus
Cauchy fillings.

These are finite implementation checks, not proofs of the universal analytic
theorems or the iPRA metatheorems.

## Rebuild the PDF

With a normal TeX Live installation containing AMS, Latin Modern, geometry,
microtype, hyperref, xurl, listings, and TikZ:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

Alternatively run `pdflatex` three times. The source is standalone and requires
no external figures, bibliography database, network, or shell escape.

## ProveIt baseline

Inspected revision:

    0bba41d70f061442357cae0f6de055434a33fb09

Toolchain: `leanprover/lean4:v4.32.0`.

The relevant deeply embedded foundations are under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.
The source manifest records exact Git blob identifiers and SHA-256 hashes.
The existing repository build was not rerun. This deliverable is an archive;
no repository commit or pull request was made.
