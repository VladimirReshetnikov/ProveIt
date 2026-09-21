# Surcomplex Polynomial Algebra

**Ordered Geometry, Valuative Root Trees, and Residue Duality**  
Research exposition, September 21, 2026.

## Contents

- `surcomplex_polynomial_algebra.pdf` — the 33-page article (title page, contents, and 31 numbered pages).
- `surcomplex_polynomial_algebra.tex` — standalone LaTeX source with its bibliography.
- `verify_examples.py` — executable exact symbolic checks.
- `verification_report.txt` — the actual report: all 116 checks passed.
- `requirements.txt` — pinned dependency for the verification script.
- `artifact_validation.txt` — compilation and document-validation summary.

## Mathematical scope

The article develops finite polynomial algebra over SC = No[i] in set-sized,
algebraically closed Hahn workspaces. It proves ordered Gauss–Lucas, an
ordered-disk polynomial Rouché theorem, Hermite signature counting,
Newton-polygon and residue-subdisk root counts, strong coprime factor lifting,
exact valuative Rolle counts, critical-point branch polynomials, tree formulas
for discriminants, and a coefficient-precision theorem preserving every
pairwise root separation.

For global systems F_i = x_i^(d_i) + E_i with total degree E_i < d_i, it proves
finite freeness over arbitrary commutative coefficient rings, constructs a
perfect residue pairing and its Bézoutian kernel, and establishes the
Jacobian trace formula through collisions. Under additional positive-support
hypotheses it identifies this algebraic residue with the polynomial restriction
of the contour functional in the supplied research manuscript.

The text explicitly separates global polynomial quotients from finite-monad
analytic quotients. It does not discard the lower-degree hypothesis, assert
that all analytic perturbations satisfy the polynomial comparison theorem,
or claim to solve a named open conjecture. Established predecessors and the
two supplied manuscripts are identified in the text and bibliography.

## Compile

With a TeX distribution containing the standard packages named in the source:

```sh
latexmk -pdf surcomplex_polynomial_algebra.tex
```

Alternatively, run `pdflatex` repeatedly until cross-references stabilize.
No images, external bibliography database, or bibliography processor are needed.

## Run the checks

The recorded run used Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r requirements.txt
python verify_examples.py
```

The script writes `verification_report.txt` beside itself, and raises an error
if a check fails. Computations use exact symbolic arithmetic, without numerical
root approximations or network access. The formal parameter t is used only for
finite rational-function valuations and formal coefficient checks; the script
does not implement the entire surreal field.

## Verification limits

The 116 tests concern examples and finite identities. They are not a formal
verification of the general proofs, arbitrary Hahn supports, transfinite
recursion, class-set foundations, or real-closed-field transfer. The article
supplies mathematical proofs but has not been independently refereed or
machine-checked. No exhaustive novelty or priority certification is claimed.

The two original uploaded manuscripts are referenced, not modified or included
as duplicate files in this archive.
