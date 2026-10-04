# The Baker–Campbell–Hausdorff Formula
## Complete Proofs, All-Order Expansions, and Analytic Qualifications

A mathematical paper prepared on 16 September 2026 in response to a request
for proofs of the formulas and mathematical assertions on the English
Wikipedia page “Baker–Campbell–Hausdorff formula.”

Scope is pinned to revision **1368909113**, last edited 11 August 2026:
https://en.wikipedia.org/w/index.php?oldid=1368909113

The paper's coverage appendix maps the page's assertions and displays to
proofs, or to explicitly corrected statements where a hypothesis or formula
on the page is not valid as written. A linked theorem that is merely named,
such as Stone–von Neumann or Golden–Thompson, is not treated as a theorem
stated on the page. The relevant Weyl relations are proved directly.

## Contents

- `bch_complete.pdf` — the compiled mathematical paper.
- `bch_complete.tex` — self-contained LaTeX source, apart from the included
  coefficient table `data/word_certificate.tex`.
- `code/verify_bch.py` — dependency-free exact-rational verifier and
  coefficient generator.
- `data/bch_coefficients.json` and `data/bch_words.tsv` — all nonzero
  associative BCH word coefficients through total degree 10.
- `data/zassenhaus_coefficients.json` — all nonzero associative coefficients
  of each Zassenhaus exponent C_2 through C_10.
- `data/symmetric_bch_coefficients.json` — the logarithm of
  exp(X/2) exp(Y) exp(X/2), through degree 10.
- `data/word_certificate.tex` — complete degree-5 and degree-6 tables,
  including zero coefficients, included in the paper.
- `data/verification_results.json` — named checks, outcomes, and counts.
- `data/verification_log.txt` — output from the included verification run.
- `COVERAGE.md` — a compact scope and corrections guide; the detailed
  formula-by-formula index is in Appendix D of the paper.
- `source_inventory.json` — pinned page and primary research references.
- `Makefile` — optional build and verification shortcuts.

## Principal mathematical constructions

The paper proves a finite cut formula for every associative BCH coefficient,
a finite nested-commutator formula for every bihomogeneous component,
Dynkin's full formula, the Dynkin–Specht–Wever projection, Friedrichs'
primitive-element characterization, and the PBW input needed for universal
specialization to arbitrary Lie algebras. An independent Bernoulli
differential construction proves the Poincaré integral formula and recursions
for all homogeneous components and all powers of the second variable.

For Zassenhaus, the paper proves existence and uniqueness, residual and
differential algorithms, an ordered-partition recurrence, a finite weighted
plane-tree formula with no unknown coefficients, and a quantitative norm
convergence criterion. Further results include local Lie correspondence,
integration from simply connected groups, nilpotent polynomial group laws,
Trotter and Suzuki product formulas with full local logarithmic error series,
all-order Maurer–Cartan and invariant-metric expansions, and quantum identities
proved in Schrödinger and Bargmann–Fock realizations.

## Important distinctions and corrections

1. Formal identities, convergent local identities, and global resummed
   exponential identities are distinguished throughout.
2. Infinite-series coproducts take values in a completed tensor product;
   normalized grouplike elements have constant term 1.
3. The coframe matrix is W = phi_-(ad_X), not the adjoint matrix ad_X.
   Expressions with division by ad_X are analytic functional calculus,
   not literal inversion of that singular matrix.
4. The Killing form can be degenerate. Pullback tensors need additional
   hypotheses to be metrics, and arbitrary maps need Jacobian factors.
5. Trace identities require the BCH logarithm branch; other logarithms have
   a 2*pi*i integer trace ambiguity.
6. A central commutator on a dense domain alone does not imply all Weyl
   relations for unbounded operators. The paper gives a concrete
   counterexample as well as direct proofs in valid representations.

## Reproduce the computations

Python **3.10 or later**, no third-party packages:

```sh
python3 code/verify_bch.py --degree 10 --output data
```

The included run passed **20 exact checks**. Most are through degree 10;
independent exhaustive cut enumeration and unshuffle coproduct checks are
through degree 8, and three-letter associativity is through degree 6.
The displayed page formulas are checked through their entire displayed
degrees: BCH through 6 and Zassenhaus through 4. The weighted-tree formula
is explicitly enumerated and checked through 10.

All computations take place in a truncated **free associative algebra over
rational numbers**. These are not floating-point or random matrix tests.
The finite checks do not replace, or claim formal verification of, the
paper's all-order and analytic proofs.

The command permits degrees 6 through 12. A different degree overwrites the
coefficient data and run metadata; the paper's reproducibility description
reports the supplied degree-10 run. To retain it, select another output
folder for experiments.

## Compile the PDF

A standard TeX installation with `pdflatex` and the packages declared in the
preamble is sufficient. No bibliography processor, internet access, shell
escape, or custom font files are required.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error bch_complete.tex
```

Without `latexmk`, run `pdflatex bch_complete.tex` repeatedly until
cross-reference warnings disappear. The optional Makefile provides
`make pdf`, `make verify`, and `make clean`.

## Coefficient conventions

Words such as `XXY` in JSON and TSV denote **associative monomials**, not
nested commutators. Their coefficients are rational strings. Absent words
have coefficient zero. In the paper, a right-bracket marker denotes
[X,[X,Y]], and the right Dynkin projection converts word coefficients to
Lie expressions by dividing the bracketing map by total degree.
The Bernoulli convention is B_1^+ = +1/2.
