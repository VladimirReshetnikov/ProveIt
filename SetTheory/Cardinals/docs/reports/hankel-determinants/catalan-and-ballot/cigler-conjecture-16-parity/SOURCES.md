# Sources and bounded literature audit

Consulted on 20 September 2026. Only the sources actually used are listed here;
this is not an exhaustive bibliography of Hankel determinants.

## 1. Exact primary problem

Johann Cigler, *Hankel determinants of middle binomial coefficients and
conjectures for some polynomial extensions and modifications*,
arXiv:2111.14492v3 (30 December 2021).

- Record: https://arxiv.org/abs/2111.14492v3
- PDF: https://arxiv.org/pdf/2111.14492v3
- Equation (6), printed p. 3: the source moments `c_n(t)`.
- Section 5, printed pp. 19–21: different moment family `a_n(t)` and
  Conjectures 13–15, the family already represented in the supplied manifest.
- Section 6, printed pp. 21–22: determinant definition (76), normalization
  (78), and **Conjecture 16**, including stable-coefficient equations (79)–(80).
- Printed p. 22: small-shift formulas and sample polynomials used as indexing
  checks. These pre-existing examples are not claimed as new results.
- Conjectures 17 and 18 give stronger statements beyond the selected target;
  this package does not claim to settle all of them.

The formula pages were checked as rendered PDF images, not solely through
machine-extracted text. The source uses `d_k` without the parity-dependent
sign adjustment; the article uses `H_k` with that adjustment. The difference
is explicitly accounted for throughout.

## 2. Classical framework

Johann Cigler and Christian Krattenthaler, *Hankel determinants of linear
combinations of moments of orthogonal polynomials*, arXiv:2003.01676 (2020).

https://arxiv.org/abs/2003.01676

Used to credit the surrounding moment/orthogonal-polynomial framework. The
specific moment-modification identity needed in the argument is proved in
Section 6.1 of the article rather than imported without proof. No subsequent
publication history or bibliographic detail beyond the checked arXiv record
is needed for the argument.

## 3. User-supplied selection constraint

Vladimir Reshetnikov, *A manifest of docs/reports: Seventy-one independent
mathematical research packages, classified by subject*, `manifest.tex`,
dated 20 September 2026, supplied with the request.

The relevant entry is **Product formulas for ballot-polynomial Hankel
determinants**, under **Catalan and ballot moments**, reporting proposed
solutions of Cigler's Conjectures 13–15. The full supplied manifest was read
when selecting a nonduplicate target. It cautions that its summaries record
the reports' claims, not independently checked proofs. Its role here is an
exclusion list and a guide to related subject matter, not proof evidence.

The supplied file is not redistributed or modified in this package.

## 4. A similarly titled but different conjecture

The search surfaced Manuel Kauers, *A Proof of Conjecture 16*, with the
author-hosted URL:

https://www.algebra.uni-linz.ac.at/people/mkauers/publications/kauers26a.pdf

Search-index excerpts on the author's institutional domain identify the
subject as **A339987**, a graph-enumeration sequence, rather than Cigler's
polynomial moment conjecture. The complete PDF was not successfully fetched.
Accordingly, the audit uses only that narrow indexed disambiguation; it does
not pretend to have read the full talk or use it as a proof source.

## 5. Search scope and uncertainty

Targeted searches included the paper identifier and title, and combinations
such as:

- `"2111.14492" "Conjecture 16" proof`
- `"Cigler" "Conjecture 16" Hankel proof`
- `"kauers26a.pdf" "Conjecture 16"`
- `site.algebra.uni-linz.ac.at/people/mkauers "Conjecture 16" "A339987"`

The search did not locate a later solution of Cigler's specific Conjecture 16.
Some queries returned irrelevant material; such results were not treated as
mathematical evidence. An absence of matching results does not rule out a
proof under a different title, unindexed work, or unpublished knowledge.
The article therefore presents a proposed solution to a published conjecture
without an absolute priority assertion.
