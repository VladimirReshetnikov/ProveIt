# Sources, version audit, and duplicate avoidance

Research date: 20 September 2026.

## Requested basis: supplied manifest

Vladimir Reshetnikov, *A manifest of docs/reports*, 20 September 2026,
user-supplied `manifest.tex` (71 packages). The full uploaded file was read.
The original is copied unchanged to `inputs/manifest.tex` for provenance.

Relevant entry:

> Product formulas for ballot-polynomial Hankel determinants

Directory recorded there:
`hankel-determinants/catalan-and-ballot/ballot-polynomial-hankel-determinants`.
Its stated target is Cigler's **Conjectures 13, 14 and 15 in Section 5**.

The present target is **Conjecture 8 in Section 4**, for the b_m(t) middle-
binomial extension, not that Section 5 ballot-moment family. The manifest
itself cautions that its entries record draft claims rather than checked
proofs. It is used only for selecting a related but nonduplicate problem.

## Primary mathematical problem source

Johann Cigler, *Hankel determinants of middle binomial coefficients and
conjectures for some polynomial extensions and modifications*.

- Version-specific record: https://arxiv.org/abs/2111.14492v3
- Version-specific PDF: https://arxiv.org/pdf/2111.14492v3
- Current record checked: https://arxiv.org/abs/2111.14492
- DOI: https://doi.org/10.48550/arXiv.2111.14492

The arXiv record stated submission 29 November 2021 and last revision
30 December 2021 (v3). This was the current version shown when checked.

Relevant source locations:

- Equation (4), printed page 3: the binomial definition of b_m(t).
- Section 4: shifted Hankel determinants of that family and their normalization.
- Equation (53), printed page 16: the k=2 normalized formula already known
  in the source; it is reproduced only as a convention check.
- Equation (55), printed page 16: r_(2k)=d_(2k), the even-shift normalization.
- Conjecture 8, printed pages 16–17.
- Equations (56) and (57), printed page 17: numerator form, exact block
  degrees, and complementary reciprocity.
- Conjecture 10, printed pages 17–18: the adjacent generating-function
  question; the new article obtains its denominator but makes no claim about
  the separately conjectured numerator degree and reciprocity.

The PDF text extraction is imperfect. Rendered source page images were used
for the moment definition and the page introducing Conjecture 8, and the
formulas were cross-checked against the source's explicit low-k examples.
Some later screenshot fetches returned tool errors; the parsed equation (56)
and (57) text was available and the stated formulas match those examples.
No third-party paper is redistributed in this package.

## Classical mathematical ingredients

William Fulton, *Young Tableaux: With Applications to Representation Theory
and Geometry*, Cambridge University Press, London Mathematical Society
Student Texts 35, Parts I–II.

Publisher page directly consulted for the Schur-module character statement:
https://www.cambridge.org/core/books/abs/young-tableaux/representation-theory/A55CC8329800BD5E7E65EF75B6DEAE5C

Chapter DOI: https://doi.org/10.1017/CBO9780511626241.010

The publisher's summary explicitly states that the semistandard tableau
basis consists of diagonal eigenvectors with tableau weight monomials and
that the representation's character is the Schur polynomial. That theorem
is imported, not newly proved here. The article separately explains the
SL(2) restriction and the weight-string consequence for unimodality.

I. G. Macdonald, *Symmetric Functions and Hall Polynomials*, second edition,
Oxford University Press, 1995, Chapter I, is a standard bibliographic reference
for Jacobi–Trudi, dual Jacobi–Trudi, and the alternant formula. This is a
reference to classical mathematics, not a claim to have newly retrieved or
read the complete book during this session.

## Public literature search and its limits

Representative searches actually made included:

- `"Cigler" "Conjecture 8" "Schur"`
- `"middle binomial" "Hankel" "Schur"`
- `"2111.14492" proof polynomial`
- `"Cigler" "palindromic" "unimodal" Hankel`
- `"Hankel determinants of middle binomial" "Schur polynomials"`
- `"Cigler" "2111.14492" "proof"`
- `"Hankel determinants of middle binomial" proof conjecture`

Cigler's preprint list was also consulted:
https://homepage.univie.ac.at/johann.cigler/prepr.html

Recent Hankel literature was checked to avoid mistaking differently numbered
conjectures for this one. In particular, the August 2026 paper by Shane Chern
and Wenle Shi, *Hankel determinants of Catalan-like sequences*,
https://arxiv.org/html/2608.27208v1, concerns a different Catalan-like setup
and different conjecture numbering. It is not used in the proof.

These searches did not locate a prior resolution of Conjecture 8 of
2111.14492v3. They do not establish exhaustive bibliographic novelty, nor
exclude an unpublished proof. The article's mathematical claims are supported
by its derivations rather than by an assumption that no one proved them before.
