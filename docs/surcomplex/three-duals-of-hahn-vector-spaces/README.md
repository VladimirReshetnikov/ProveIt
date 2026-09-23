# Three Duals at Surreal Scales

**Strong Hahn Operators, Completion Defects, and Invisible Functionals**  
Research manuscript, September 22, 2026.

## Files

- `article.pdf`: typeset article, 27 pages (title, contents, 24 numbered pages).
- `article.tex`: self-contained LaTeX source with an embedded bibliography.
- `verify_examples.py`: reproducible finite checks using exact rational arithmetic.
- `verification_report.json`: recorded result of the checks: 610 assertions passed.
- `source_audit.md`: repository revision, consulted sources, and novelty boundary.

## Main results

The article studies the set-sized Hahn vector space V((t^Gamma)) over
K = k((t^Gamma)). It identifies the valuation completion of K tensor_k V
with the series having finite coefficient rank below every valuation cut.
It classifies all strong K-linear operators by one global Hahn expansion
of arbitrary k-linear coefficient maps, and gives the continuous dual an
exact restriction sequence. Its invisible kernel separates precisely the
vectors outside the completed algebraic scalar extension.

For infinite-dimensional V and nonzero Gamma, the algebraic scalar
extension is dense in the full Hahn space exactly when Gamma is ordered
isomorphic to Z. It has a proper completion exactly when Gamma has
countable cofinality. The article gives the resulting three-way
classification, including the case in which the algebraic scalar
extension is complete but still smaller than the Hahn space.

For an ordinary infinite-dimensional complex Hilbert space, the
inner-product-represented, strong, and valuation-continuous duals are
strictly nested for every noncyclic nonzero exponent group. A cofinality
criterion describes exactly how completion changes when more exponent
scales are admitted. The explicit surreal-scale example contrasts the
powers omega^(-n) with the new tolerance omega^(-omega).

## Build the PDF

Use a TeX distribution with the packages named in the preamble:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively, run `pdflatex -interaction=nonstopmode -halt-on-error
article.tex` three times. The bibliography is included in the TeX file;
BibTeX is not needed. No external figures or font files are required.

## Reproduce the finite checks

Python 3.10 or later; standard library only:

```sh
python verify_examples.py
```

The script writes `verification_report.json`. It uses `fractions.Fraction`
throughout and seed 20260922. An alternate report path may be specified:

```sh
python verify_examples.py --output another_report.json
```

The finite computations verify convolution identities, coefficient ranks,
projection identities, and finite support examples. They do not verify
infinite support arguments, completion, Hahn--Banach extension, Hamel-basis
existence, or priority. The general results are proved in the article.

## Mathematical and bibliographic status

This manuscript supplies complete written proofs of its stated results,
with classical inputs identified. It does not claim to solve a named
published conjecture. The precise completion/duality/enlargement package
was not located in the targeted repository and primary-literature review,
but this is not a certification of originality or priority.

The proofs have not been independently refereed or checked in Lean or
another proof assistant. The repository's existing automatic-adjoint and
Hahn--Hilbert results are not claimed as new here. See Section 13 and
`source_audit.md` for the comparison and its limits.

All Hahn fields, supports, index sets, and choices used in the proofs are
sets. The connection to surreal and surcomplex numbers is through fixed
normal-form workspaces, not a class-sized Hahn--Banach construction.
