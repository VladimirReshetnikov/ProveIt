# Source audit and provenance

## Fixed repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Inspected commit: `e9c09b12549ea4e3bea7cebc52b450b761f6f581`.
The commit metadata was read through the connected GitHub tool. Its UTC
commit date is 2026-09-30; the article is dated 29 September in the user's
US Pacific date context.

Primary repository article:

https://github.com/VladimirReshetnikov/ProveIt/blob/e9c09b12549ea4e3bea7cebc52b450b761f6f581/SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity/article.tex

Title: *A parity factorization and sharp stabilization for Cigler's Hankel
polynomials*, 20 September 2026.
Git blob: `f33543af1f846c24511dc3004fb3542c2a20c50f`.

Relevant content actually read: definitions; the auxiliary Gram identity;
all four parity factors; the explicitly nonminimal recurrence; the
experimental rectangular-Schur conjecture; first-defect and convergence
statements; the status/exclusions. The formula labeled `eq:schur-candidate`
in Section 10 is explicitly unproved in that report.

Related report, actually read for distinction and methodology:

https://github.com/VladimirReshetnikov/ProveIt/blob/e9c09b12549ea4e3bea7cebc52b450b761f6f581/SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-8-schur/article.tex

Title: *Rectangular Schur Polynomials and Cigler's Conjecture 8*.
Git blob: `9c984baeebb8ba13e22ea2f8ba123f09998b350b`.
This concerns b_n(t), not the selected c_n(t). It uses a Laurent-Gram basis
change and Schur identities. The present article credits that connection.

Repository discovery searched for open conjectures and then for Cigler/Schur
matches. The result is a bounded audit of the identified reports, not a claim
to have read every document in the rapidly changing repository.

## Primary literature consulted

1. Johann Cigler, *Hankel determinants of middle binomial coefficients and
   conjectures for some polynomial extensions and modifications*,
   arXiv:2111.14492v3 (30 December 2021).
   https://arxiv.org/abs/2111.14492
   https://arxiv.org/pdf/2111.14492
   The abstract/version record and Section 6 were inspected. PDF images of
   printed pages 21-24 were read because parsed mathematics was garbled.
   Page 24 was checked again for equations (84)-(87) and the small-shift
   generating functions. Equation (85)'s missing sign is a direct source
   comparison, not inferred from a secondary summary.

2. Mihai Ciucu and Christian Krattenthaler, *A factorization theorem for
   classical group characters, with applications to plane partitions and
   rhombus tilings*, arXiv:0812.1251; Springer volume (2010), pp. 39-60.
   https://arxiv.org/abs/0812.1251
   The record/abstract establish the existing rectangular-character
   factorization background. The specific Toeplitz formula needed here is
   proved in the new article, not taken from an unread theorem in this paper.

3. Per Alexandersson, *Stretched skew Schur polynomials are recurrent*,
   Journal of Combinatorial Theory A 122 (2014), 1-8.
   https://arxiv.org/abs/1210.0377
   https://doi.org/10.1016/j.jcta.2013.09.009
   The record/abstract establish that general recurrence existence and work
   on minimal recurrences predate this article. No solution of all of that
   paper's conjectures is claimed.

4. Luis Angel Gonzalez-Serrano and Egor A. Maximenko, *Bialternant formula for
   Schur polynomials with repeating variables*, arXiv:2312.15680;
   Linear and Multilinear Algebra (2025).
   https://arxiv.org/abs/2312.15680
   https://doi.org/10.1080/03081087.2025.2464639
   The record/abstract establish the existing repeated-variable bialternant
   theory. The elementary Taylor confluence needed for this article is
   explained explicitly; the nonzero leading-coefficient formula is derived.

5. William Fulton, *Young Tableaux*, Cambridge University Press, 1997.
   A standard background reference also cited in the repository's Schur
   article. Used for classical Jacobi-Trudi/character facts, not for a claim
   that an unread page contains a new formula from this article. No full
   electronic copy of the book was inspected in this session.

## Bounded novelty/status search

Queries included the exact arXiv identifier and title; Cigler with
"Conjecture 16", "Conjecture 18", "Schur", and "proof"; rectangular Schur
factorizations; stretched Schur recurrences; and confluent Schur/minimal
recurrence combinations. Relevant primary results are listed above.
Some searches returned irrelevant material and were not used as evidence.

The inspected source still presents the selected original questions as
conjectures, and the pinned repository explicitly labels its Schur identity
experimental. These facts establish the problem's provenance, not an
exhaustive certificate of global historical priority. The article's
mathematical claims are supported by its proofs, not by an absence of
search hits.
