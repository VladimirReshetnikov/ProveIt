# Hilbert Geometry at Surreal Scales

**Orthogonal Splitting, Amplified Graphs, and Fredholm Least Squares**  
Research manuscript prepared for Vladimir Reshetnikov — September 23, 2026.

## Contents

- `article.pdf`: the 29-page typeset article, including a title page, contents,
  complete main proofs, a hypothesis checklist, and references.
- `article.tex`: self-contained LaTeX source; the bibliography is embedded.
- `checks.py`: supplementary exact symbolic identity checks.
- `proof_audit.md`: a theorem/dependency ledger and review limitations.
- `verification/check_results.json` and `verification/check_results.txt`:
  the recorded successful symbolic-check output.
- `verification/build_report.txt`: compilation and visual-review record.

## Main results

The model is H((t^Gamma)), with ordinary real or complex Hilbert coefficients
and an arbitrary nonzero set-sized ordered abelian value group. Inner products
first use ordinary Hilbert summation within a coefficient and then Hahn
convolution across exponents. Divisibility is not assumed.

Theorem 6.5 gives the residue normal form for every orthogonally split subspace,
using the repository's automatic adjoint theorem and a classical direct rotation.
Theorem 7.2 proves that the graph of an infinitely amplified ordinary bounded
operator is orthogonally split exactly when the ordinary operator has closed
range. Finite amplifications always have split graphs.

Theorem 8.2 shows that the orthogonally split-subspace poset is a lattice exactly
when the ordinary coefficient Hilbert space has finite dimension. The explicit
counterexample in infinite dimension consists of two split subspaces with no
meet in this poset; it is not merely a nonclosed intersection.

Theorems 9.1, 10.1 and 11.2 reduce positive-order perturbations of ordinary
Fredholm operators to a finite Schur matrix, construct their exact adjointable
Moore–Penrose inverses, and determine the inverse valuation from consecutive
minimal minor valuations. All least-squares problems then have minimum-norm
solutions.

Section 12 treats scalar extension and separately gives a literal full
surcomplex vector-class formulation in NBG class theory. Theorem 12.2 proves
that an everywhere-defined adjointable global operator still has one set-sized
support of ordinary bounded coefficient operators. This does not identify
full-surreal fine convergence with convergence in a fixed Hahn workspace.

## Build the PDF

A standard TeX Live installation with pdfLaTeX and the packages listed in the
preamble is sufficient. No external images or bibliography database are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Without latexmk, run pdfLaTeX three times to resolve the contents and references.
The source and PDF in this archive match. No font files or build intermediates
are included.

## Run the finite checks

Use Python 3.10 or later with SymPy installed, then run:

```sh
python checks.py
```

The recorded run used Python 3.13.5 and SymPy 1.14.0. It passed 16 named checks,
including 125 triangular exponent triples. The script uses exact rational and
complex-rational symbolic arithmetic, not floating-point sampling.

The checks concern finite identities only. They are not a machine verification
of infinite-dimensional support, completeness, automatic adjoints, or the class
argument. They do not establish novelty.

## Provenance and mathematical status

Repository snapshot inspected:
`9a385d3957bdfe3d9ea79f9a524751c90bd2c894`
in `VladimirReshetnikov/Surreal`.

The construction, automatic adjoint theorem, non-Archimedean duality obstructions,
and classical projection/perturbation tools are credited in the article.
The candidate original packages are distinguished from those inputs. The
literature and repository comparison was targeted, not exhaustive; some source
access was limited as recorded in Section 13. No named published conjecture is
claimed solved. The manuscript has not been independently refereed or formally
verified in Lean or another proof assistant.

No repository files were modified, and no changes were committed or uploaded.
