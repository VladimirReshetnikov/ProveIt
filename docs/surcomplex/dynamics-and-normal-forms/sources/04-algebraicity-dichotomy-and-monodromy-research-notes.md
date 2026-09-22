# Provenance and research audit

## Repository baseline

Repository: https://github.com/VladimirReshetnikov/Surreal

Frozen baseline: `39f2be6667ade51bca2b45daa47e289d69c09764`.

The GitHub connector was used to retrieve the recursive tree, documentation
map (`docs/README.md`), catalogue (`docs/manifest.tex`), and the foundational
surcomplex analysis source. The map distinguishes seven surcomplex report
families and explicitly warns about non-equivalent coefficient rings.
The article uses that distinction, works in a fixed common-domain Hahn ring,
and does not use unverified advanced conclusions from the repository as
premises in its main proofs.

This was a targeted inspection, not an exhaustive line-by-line audit of
all repository files or all historical revisions. No repository changes
were made.

## Primary literature used

1. B. H. Neumann, *On ordered division rings*, Transactions of the AMS 66
   (1949), 202–252. DOI: 10.1090/S0002-9947-1949-0032593-5.
   The classical positive-support/finite-factorization lemma is an explicit
   foundational dependency, not a new result of this article. Publication
   metadata and the standard lemma were cross-checked; the publisher's
   direct PDF endpoint was not accessible in this session.

2. Karl-Olof Lindahl, *Linearization in ultrametric dynamics in fields of
   characteristic zero—equal characteristic case*, p-Adic Numbers,
   Ultrametric Analysis and Applications 1(4) (2009), 307–316.
   https://arxiv.org/abs/1111.1993
   The paper supplies the relevant established equal-characteristic-zero
   ultrametric linearization setting and sharp radius phenomena. The
   present article does not claim the quadratic disk scale as an isolated
   new classical result.

3. Vassili Gelfreich and Arturo Vieiro, *Interpolating vector fields for near
   identity maps and averaging*, arXiv:1711.01983 (2017).
   https://arxiv.org/abs/1711.01983
   The paper explicitly discusses the established formal embedding of
   near-identity maps and the distinction from analytic embedding at a
   nonzero numerical parameter. Our formal logarithm is not presented as
   an invention of that mechanism.

4. Elliot Kaplan, Lothar Sebastian Krapp, and Michele Serra, *Decomposing
   the automorphism group of the surreal numbers*, arXiv:2509.22374v3,
   revised 23 April 2026.
   https://arxiv.org/abs/2509.22374v3
   Relevant for the current generalized-series setting and the relation
   between strongly linear automorphisms and derivations.

The article includes its own ordinary LaTeX citations and bibliography.
No publisher PDFs, repository documents, or third-party source manuscripts
are redistributed in this archive.

## Precisely what is proposed as a contribution

The principal candidate contribution is the combination of:

- the polynomial Euler-map algebraicity dichotomy over the large field
  C(w)((t^Gamma)), not merely over C((t^Gamma))(w);
- the exact coefficientwise monodromy exponent and its finite-cover
  obstruction, including cases with algebraic leading coordinate;
- the classification of algebraic leading coordinates and the proof that
  the first infinitesimal correction is already transcendental in those
  nonlinear cases;
- the support-controlled bridge between an exact inner Taylor disk and a
  common-domain continuation at the critical infinitesimal scale.

The construction of formal logarithms, ordinary integration of a
one-dimensional linearizing differential equation, and rank-one
ultrametric radius theory are acknowledged precedents. The literature
search was bounded and did not certify priority. No named published open
problem is claimed solved.

## Verification boundary

The mathematical argument is separate from the computational checks.
The program verifies recurrence coefficients, directly substituted finite
Schroeder residuals, logarithmic generator identities on monomials, fixed
point derivatives, and the first two analytic coefficient formulas, all
using rational arithmetic. The recorded run passed 2,764 assertions.

No Lean, Wolfram, or other proof-assistant verification of the new infinite
statements was performed. The paper is not peer reviewed. A successful
program run is not evidence of exhaustive novelty or formal correctness
of every theorem.

## Artifact checks

The final PDF was compiled with all cross-references resolved and no
LaTeX warnings or overfull/underfull boxes in the final log. The document
was rendered to page images and visually inspected, including the title,
contents, principal theorem, monodromy proof, worked expansion, tables,
and references. It is a 23-page A4 article. Intermediate build products are
not part of the archive.
