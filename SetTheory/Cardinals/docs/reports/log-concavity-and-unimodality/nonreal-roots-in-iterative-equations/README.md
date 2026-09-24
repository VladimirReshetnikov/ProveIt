# Nonreal Roots Survive in Polynomial Iterative Equations

**A cubic counterexample and a classification of circular spectra**  
Research draft prepared for Vladimir Reshetnikov — 20 September 2026

## Result at a glance

For a polynomial P(z) = sum a_j z^j, the notation P[f] means
sum a_j f^{∘j}, not a polynomial in the pointwise values of f.

The selected target is Problem 6.1 of Szymon Draga and Janusz Morawiec,
*Reducing the polynomial-like iterative equations order and a generalized
Zoltán Boros' problem*, Aequationes Mathematicae 90 (2016), 935–950;
arXiv:1503.00570v2, preprint page 13.

The proposed deletion of nonreal maximal-modulus characteristic roots is
false under the question's stated hypotheses. The article gives an odd,
increasing, globally bi-Lipschitz homeomorphism F of the real line with

    F^{∘3}(x) = 8x,     F(1) = 3,     minimal polynomial = z^3 - 8.

Its orbit at 1 begins 1, 3, 4, 8, 24, 32, ... . The exact determinant

    det [[1,3,4], [3,4,8], [4,8,24]] = -56

rules out every lower-order relation. Deleting the nonreal roots would
force F(x)=2x, which already fails at x=1.

A globally real-analytic second example is

    h(t) = t + sin(pi*t/2)/4,
    f(x) = h(h^{-1}(x) + 1).

Its minimal polynomial is (z-1)^2(z^2+1). The reduced real-only relation
f^{∘2}(x)-2f(x)+x=0 fails at x=0, with residual -1/2.

Beyond these examples, the article classifies exactly which real monic
polynomials supported on one circle |z|=r can be the minimal iterative
polynomial of an increasing homeomorphism of R:

* For r != 1: the positive root r has odd multiplicity, no smaller than any
  other root's multiplicity.
* For r = 1: either the polynomial is z-1, or the multiplicity of 1 is even
  and strictly larger than every other multiplicity.

The necessity and constructive sufficiency proofs are self-contained.
Further results give increasing-solution rigidity criteria, quantitative
bi-Lipschitz constructions, and differentiability thresholds.

## Read first

`article.pdf` is the 21-page article; `article.tex` is its complete source.
Sections 2 and 3 contain the two counterexamples. Theorem 6.1 is the
classification. Sections 8 and 9 give the rigidity and regularity results.

`STATUS.md` separates proved mathematical statements from computational
checks, priority uncertainty, and questions not addressed.

## Reproduction

Python 3.9 or later is enough for all exact certificates. No third-party
Python package is required for the verifier:

    python code/verify.py

Run normally, not with `python -O`: the verifier deliberately refuses to
run when assertions are disabled. It writes `data/exact_certificates.json`.
The supplied run checks 4,026 rational points and computes four exact
Hankel determinants, including a degree-15 mixed-multiplicity example.
The finite sample tests supplement, and do not replace, the all-real proofs.

A separate floating-point illustration requires only the standard library:

    python code/analytic_demo.py

Optional plot regeneration requires matplotlib:

    python -m pip install -r requirements-optional.txt
    python code/analytic_demo.py --plots

The PDF figures are already included, so plotting is not needed to compile
the article. A reasonably complete TeX Live or MiKTeX installation with
`newtx`, `xurl`, and the other packages declared in `article.tex` is needed:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

No bibliography processor is required. A Makefile supplies equivalent
`verify`, `illustrations`, `pdf`, and `clean` targets. These commands also
work directly from a Windows terminal with Python and LaTeX on PATH.

## Package contents

- `article.tex`, `article.pdf`: source and final article.
- `code/verify.py`: exact rational checker with independent cubic implementations.
- `code/analytic_demo.py`: numerical illustration and optional plot generator.
- `data/exact_certificates.json`: full matrices, polynomial coefficients, and results.
- `data/numerical_illustration.json`: explicitly noncertifying floating-point results.
- `data/selection.json`: the original random draw and all 80 candidate areas.
- `figures/*.pdf`: the two vector illustrations used by the article.
- `notes/literature_audit.md`: source identifiers, what was checked, and search limits.
- `notes/selection_and_exclusion.md`: random-draw and manifest-exclusion record.
- `manifest_entry.tex`: suggested entry for a future exclusion manifest.
- `checksums.sha256`: hashes of the distributed files other than itself.

The input manifest is not redistributed or modified.

## Research status

This package supplies a negative answer to the published question as stated.
It is an AI-assisted research draft, not independently refereed and not
checked in a proof assistant. A targeted literature search did not identify
an earlier explicit answer, but it does not establish historical novelty.
The conjugacy method itself is not claimed as new. The classification is
restricted to increasing homeomorphisms and a single spectral circle;
it is not a complete classification of arbitrary polynomial iterative equations.
