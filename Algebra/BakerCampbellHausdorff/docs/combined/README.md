# The Baker–Campbell–Hausdorff Formula
## A Unified Treatment with Complete Proofs, All-Order Expansions, and Analytic Qualifications

This directory contains a single article that consolidates the three
independent treatments in `../paper-1`, `../paper-2`, and `../paper-3` of the
mathematical content of the English Wikipedia page
“Baker–Campbell–Hausdorff formula”, pinned to revision **1368909113**
(last edited 11 August 2026, consulted 16 September 2026):
https://en.wikipedia.org/w/index.php?oldid=1368909113

For every result the article keeps the most complete or most elementary of
the three arguments, includes every construction that appeared in only one
of the sources, and writes all proofs out in full. Appendix C is a
claim-by-claim concordance with the page; corrected or qualified assertions
are identified as such.

## Contents

- `bch_combined.pdf` — the compiled article (75 pages).
- `bch_combined.tex` — main LaTeX file; the sections are in `tex/`.
- `tex/01_scope.tex` … `tex/14_computation.tex` — the fourteen sections.
- `tex/appendix_pbw.tex` — ordered PBW theorem, enveloping Hopf algebras,
  and the completed-tensor-product counterexample.
- `tex/appendix_tables.tex` — coefficient certificates (generated).
- `tex/appendix_coverage.tex` — claim-by-claim coverage of the source page.
- `tex/references.tex` — bibliography.
- `code/make_tables.py` — regenerates `tex/appendix_tables.tex` from the data,
  after independently recomputing every printed low-degree coefficient by the
  finite cut formula, expanding the displayed brackets, reconstructing every
  Lyndon table, and expanding the Zassenhaus tree polynomials.
- `code/run_all_verifiers.py` — reruns the three source papers' exact
  verifiers (unchanged, from their own directories) into a scratch folder
  and writes `data/verification_summary.json`.
- `data/*.csv`, `data/*.json` — exact rational coefficient tables through
  degree 12 (copied from `../paper-2/data`) and the Zassenhaus tree
  polynomials through degree 10 (from `../paper-3/data`).
- `Makefile` — `make pdf`, `make tables`, `make verify`, `make clean`.

## What the article covers

Sections 2–4: formal exponentials, a finite nonrecursive formula for every
associative word coefficient, the completed Hopf algebra, the
Dynkin–Specht–Wever identity, Friedrichs' characterization, Dynkin's formula,
a finite formula for every bidegree, symmetries and associativity, and the
complete polynomial through degree six with a finite certificate.

Sections 5–6: Campbell's identity, the differential of the exponential,
Bernoulli coefficients (recursion, finite formula, partial fractions, zeta
values, radius 2π), the Poincaré integral, an all-bidegree operator-block
formula, every order in the number of occurrences of Y with an explicit
bivariate kernel for the quadratic part, a finite-at-each-order expansion
around a regular base point, and two total-degree recursions.

Section 7: quantitative convergence and remainder bounds, the Mercator tail,
the role of ||Z|| < log 2, the trace identity with its branch restriction,
and the sl(2) nonconvergence example with all logarithms classified.

Section 8: matrix groups, Maurer–Cartan equation, intrinsic differential of
the exponential, local BCH multiplication, local Lie correspondence,
integration from simply connected groups, nilpotent polynomial group laws.

Section 9: commuting and central commutators, several factors, the relation
[X,Y] = sY with global resummation and resonances.

Section 10: Zassenhaus factorization — existence and uniqueness, residual,
coefficient, and differential recursions, the displayed exponents, a finite
weighted-tree formula for every exponent, a globally convergent
ordered-simplex expansion, and a convergence criterion for the product.

Section 11: Trotter, symmetric, and Suzuki product formulas with complete
logarithmic error series.

Section 12: exponential coordinates, the coframe W = φ(ad X) (not ad X),
pullbacks with Jacobians, the Killing form, all-order invariant-metric and
volume-density expansions, and the rotation-group example.

Section 13: Weyl relations, the dense-domain counterexample, Bargmann–Fock
space, displacement operators with the generator identified, normal ordering,
composition law, all matrix elements, coherent states.

Section 14 and appendices: exact computations, PBW, certificates, coverage.

## Essential qualifications

The coproduct needs the completed tensor product. The trace identity concerns
the BCH branch. Smallness is sufficient, not necessary, for convergence, and a
resummed closed form can be valid where its Taylor series diverges but fails
at nonzero resonances 2πik in the shape X + cY. In exponential coordinates
M = ad X is always singular and is not the coframe; W = φ(M) is. Neither an
arbitrary pullback nor the Killing form is automatically a metric. The
alternate Zassenhaus product starting at n = 1 needs C_1 = Y. Unbounded
commutator identities require domain hypotheses; the quantum formulas are
proved in concrete representations.

## Build

A standard TeX installation (MiKTeX or TeX Live) with the packages named in
the preamble suffices; no bibliography processor, shell escape, fonts, or
internet access is needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error bch_combined.tex
```

## Reproduce the exact checks

Python 3.10 or later, standard library only:

```sh
python code/make_tables.py          # 36 exact checks, then rewrites tex/appendix_tables.tex
python code/run_all_verifiers.py    # reruns the three verifiers (about a minute)
```

The three verifiers report 20, 30, and 26 passed exact checks respectively
(76 in total); their scope is described in Section 14 of the article. These
are finite exact-rational checks in the truncated free associative algebra,
not floating-point tests and not proof-assistant certification. The
all-order and analytic statements are established by the proofs in the
article.

## Conventions

Words such as `XXY` in the data denote associative monomials, not nested
commutators. In `lyndon` files a word means the standard Lyndon bracketing
L(w) with alphabet X < Y; in the `right_commutators` file it means
R(w) = [a1,[a2,…]]. These conventions must not be interchanged: R(XYY) = 0
whereas L(XYY) = [[X,Y],Y]. The Bernoulli convention is B_1^+ = +1/2.
