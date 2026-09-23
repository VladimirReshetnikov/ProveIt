# Independent Surreal Copies and Arithmetic Intersections

A 25-page AI-assisted research article, dated 23 September 2026.

## Files

- [article.pdf](article.pdf): typeset article, 25 pages in the repository build.
- [article.tex](article.tex): self-contained LaTeX source, including bibliography.
- `README.md`: this guide and the verification boundary.

## Main results developed

**Theorem A — Prescribed independent copies.** For every set-sized divisible
ordered additive subgroup H of No, the article constructs an ordinal-indexed
family of proper strong self-embeddings of No fixing the full real Hahn field
on H. Distinct image fields intersect exactly in that Hahn field, and every
finite subfamily is jointly linearly disjoint there. The embeddings preserve
and reflect omnific integers. Complexification gives the corresponding
surcomplex and Gaussian-omnific assertions.

**Theorem B — Arithmetic intersections lose transcendental elements.** The
fraction field of the intersection of two image omnific rings is strictly
smaller than the intersection of their fraction fields. The gap is
transcendental for every set-sized Hahn core. For rational exponents, the
article supplies the explicit witness 1 + sum_{n>=1} omega^(-n!). Each of the
two image rings nevertheless provides a single denominator for the entire
common set-sized field, separately.

**Theorem C — A transcendental gap above an ordinary compositum.** For two
explicit separated-scale copies, the full Hahn field on their combined
exponent group contains an explicit countably supported surreal number
transcendental over their ordinary field compositum. The same witness works
after complexification. The proof uses a finite coefficient-field bound,
not the invalid inference that every infinite sum lies outside a compositum.

Further sections prove a coset-slice linear-disjointness lemma, describe
Boolean intersection diagrams and polynomial-relation descent, give a
conditional set-sized saturated-group analogue, and propose ten research
questions together with a formalization decomposition.

## Provenance and scope

The repository comparison is pinned to:

    VladimirReshetnikov/Surreal
    bcac55ae6fd3f2b354e568ba1d2e94d496a2cc59

The bibliography identifies the source reports and classical foundations.
The article distinguishes its proposed combined contributions from standard
Hahn-field theory and the pre-existing bounded-support transcendence
mechanism. The latter is reproved for the one-witness application rather
than claimed as a new discovery.

All supports are sets, even when an ambient exponent group or field is a
proper class. The class construction uses NBG with Global Choice. The
prescribed common field is a full Hahn field on a set-sized divisible
subgroup, not an arbitrary set-sized subfield.

## Verification boundary

Complete mathematical arguments are supplied relative to the named standard
foundations. These are proposed research results, not a certified priority
claim or a claim to have settled a named published conjecture. The manuscript
has not undergone independent peer review and is not Lean-verified.

The delivered production record reports compilation using pdfTeX 1.40.26 and latexmk.
The final LaTeX log has no undefined references, overfull boxes, or compilation
warnings. All 25 PDF pages were rendered; contact sheets and selected full-size
pages were visually inspected. These production checks are not formal
verification of the mathematics.

## Build

With a standard TeX Live installation, run:

    latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex

Alternatively run pdflatex on the source three times to resolve references
and the table of contents. No external figures, bibliography database, or
source downloads are required to build the PDF.

The source was placed as `article.tex` in `9d28e28`; the delivery used the
stem `independent_surreal_copies`. The repository build ran pdfLaTeX three
times, producing 25 pages with no warnings or unresolved references.
This build and inventory entry do not constitute mathematical proof review.
