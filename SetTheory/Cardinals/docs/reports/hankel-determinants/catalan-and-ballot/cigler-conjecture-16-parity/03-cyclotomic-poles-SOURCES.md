# Repository and literature audit

Audit date: 30 September 2026.

## Pinned repository input

Repository: https://github.com/VladimirReshetnikov/ProveIt

Commit: `ff6969475bad8f61a33268418aaf23d23fdcd1fb`

Relevant path:

    SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity/article.tex

Git blob returned by the GitHub connector:

    07c41161857ed17854b2208b66418e9d73b956d5

Immutable source URL:
https://github.com/VladimirReshetnikov/ProveIt/blob/ff6969475bad8f61a33268418aaf23d23fdcd1fb/SetTheory/Cardinals/docs/reports/hankel-determinants/catalan-and-ballot/cigler-conjecture-16-parity/article.tex

The README and Part II status file identify the report as unreviewed and not
formalized. Section 21.2 and the corresponding README/status passages explicitly
leave complex-root-of-unity spectral cancellations unclassified.

The manuscript was read through the connected GitHub tool. The relevant
sections supplied the moment definition, the Hankel--Schur identity, the
canonical confluent leading coefficient, the generic recurrence, the
negative-index framework, and the odd-shift Gram/parity identities.

## External primary sources checked

1. Johann Cigler, *Hankel determinants of middle binomial coefficients and
   conjectures for some polynomial extensions and modifications*,
   arXiv:2111.14492v3 (2021).
   https://arxiv.org/abs/2111.14492
   The original PDF and a page image of its Section 6 were inspected.
   This supplies the original moment family and conjectural context, not
   a claim that all of its conjectures are settled by the present article.

2. Luis Angel Gonzalez-Serrano and Egor A. Maximenko,
   *Bialternant formula for Schur polynomials with repeating variables*,
   arXiv:2312.15680; Linear and Multilinear Algebra (2025), pp. 2613--2647.
   https://arxiv.org/abs/2312.15680
   https://doi.org/10.1080/03081087.2025.2464639
   Background for the general repeated-variable bialternant machinery.

3. Christian Krattenthaler, *Advanced determinant calculus*,
   Seminaire Lotharingien de Combinatoire 42 (1999), Article B42q.
   https://arxiv.org/abs/math/9902004
   https://www.mat.univie.ac.at/~kratt/artikel/detsurv.html
   Classical determinant and orthogonal-polynomial context. The needed
   beta determinant is also proved directly in the article.

4. Shane Chern and Wenle Shi, *Hankel determinants of Catalan-like sequences*,
   arXiv:2608.27208v1, 27 August 2026.
   https://arxiv.org/html/2608.27208v1
   The introduction, family definitions, and principal result statements
   were inspected because this is recent work on Cigler-related Hankel
   questions. Its fixed-height Catalan-like array is a different family
   from the three-cluster rectangular characters treated in this article.

Additional searches considered recent Catalan/Narayana Hankel work and Schur
specializations at full primitive-root alphabets. Those subjects were not
used as theorem inputs here.

## Search scope and limitations

Targeted searches included Cigler with “Conjecture 16,” “roots of unity,”
“Hankel,” and repeated-variable Schur/bialternant terminology. No matching
all-shift cyclotomic pole classification was identified in the inspected
sources. This is a bounded literature audit, not an exhaustive priority
search. The contribution is therefore described as resolving the specific
repository gap, with no absolute historical-priority claim.
