# Hilbert Geometry at Surreal Scales

This directory contains base manuscript 03, placed in `a4dcb91` as
[article.tex](article.tex), with companion 06 on Hilbert foundations still
to integrate. No maintained PDF is supplied yet. Independent proof review
and Lean formalization remain pending.

The [source 03 audit](03-orthogonal-splitting-proof_audit.md) and
[source 06 audit](06-hilbert-foundations-RESEARCH_AUDIT.md) are preserved
as delivered. Their build and review claims refer to the original packages.
Code and data are prefixed `03-orthogonal-splitting-` and
`06-hilbert-foundations-` under `code/` and `data/`.

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

## Build and finite checks

Build `article.tex` with three passes of
`pdflatex -interaction=nonstopmode -halt-on-error article.tex`, or use
`latexmk -pdf article.tex`. The bibliography is embedded.

The base suite uses SymPy (the recorded run used 1.14.0) and writes beside
its own script. To preserve the delivered data, run a scratch copy:

```sh
check_dir=$(mktemp -d)
cp code/03-orthogonal-splitting-checks.py "$check_dir/checks.py"
python "$check_dir/checks.py"
```

The delivered run records 16 finite symbolic checks, including 125
triangular exponent triples. They do not verify infinite-dimensional
support, completeness, automatic adjoints or the class argument. The
companion build script uses its original package layout and is not a build
command for this report. The manuscripts' novelty and priority claims remain
subject to their stated source-review limitations.
