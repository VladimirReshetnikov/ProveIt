# Sources, provenance, and comparison scope

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Snapshot checked: `9754e83603e223811b7515eb892f22c847144593`.

Selected directory:

    SetTheory/Cardinals/docs/reports/hankel-determinants/
    catalan-and-ballot/shifted-catalan-hankel-polynomials/

The combined `article.tex` has Git blob identifier
`b29ea42fc5bba69d23c3b036bee25357e202f356`.
The pinned directory listing confirmed this blob identifier after the source
had been read. The repository index, selected provenance file, and relevant
parts of the combined article were inspected through the GitHub connector.
The original standalone Part II manuscript was also read through the user's
file library to obtain clean, line-numbered mathematical text.

The relevant earlier paper is **Root Collisions and Sharp Recurrences for
Polynomially Weighted Catalan Hankel Determinants**, dated 28 September 2026,
now included as Part II of **Shifted Catalan Hankel Polynomials**.
Its standalone Section 12.1 asks for a closed classification of cyclotomic
resonances and a uniform central-root formula. Section 12.2 asks for a
structural account of leading and higher cancellation at collided rates.

The earlier paper's own source snapshot is
`fbba58593dc0622aa914972896150d4848f935b5`. That is the earlier paper's
provenance, not the snapshot used for this new article.

The prior results used for comparison are the sector degree `k(t-k)`, the
generic order `t+1+binomial(t+1,3)`, a general finite recurrence-recovery
procedure, and separately certified central examples at t=2 and t=4.
The new article rederives all the mathematical ingredients it needs.

This was a targeted comparison with the selected report, not a proof audit
of the entire repository or of every incoming archive. Nothing was committed
to the user's repository.

## Primary literature inspected

1. Christian Krattenthaler, *Hankel determinants of linear combinations of
   moments of orthogonal polynomials, II*, arXiv:2101.04225v5 (10 September
   2021), Ramanujan Journal 61 (2023), 597–627.
   https://arxiv.org/abs/2101.04225

   Theorem 1, the confluence discussion, and Section 8 provide the classical
   comparison. General rationality and an order-at-most-2^t construction are
   not novelty claims in the present article. The source credits earlier
   work in this Catalan recurrence program. The paper and relevant formula
   pages were inspected, including rendered PDF pages.

2. Paul Barry, *Notes on the Hankel transform of linear combinations of
   consecutive pairs of Catalan numbers*, arXiv:2011.10827 (2020).
   https://arxiv.org/abs/2011.10827

   Background for the shifted-linear-multiplier topic pursued in the
   repository; not an imported proof of the new cancellation theorem.

3. Johann Cigler, *Hankel determinants of middle binomial coefficients and
   conjectures for some polynomial extensions and modifications*,
   arXiv:2111.14492 (2021).
   https://arxiv.org/abs/2111.14492

   Theorem 1, equation (23), explicitly gives the rectangular product for
   shifted middle-binomial Hankel determinants. The statement and its
   condensation proof were inspected on rendered PDF pages. The present
   central Catalan formula follows by translating x to x-2 and multiplying
   the determinant by (-1)^(Nt). It is therefore credited as known. The
   article includes a self-contained normalization and condensation proof;
   it does not claim the central product or the condensation method as new.

## Proposed contribution and limitations

The proposed extension is the complete noncentral cyclotomic minimal-
recurrence classification for one repeated root, the first centered sector
correction that proves the one-defect law, the missing-sign phenomenon,
and the resulting root-free factorization over the coefficient field.
The exact exceptional-parameter count, reflection law, and rational-input
classification are corollaries developed in the article.

The signed Vandermonde evaluation and the shift-operator minimality lemma
are elementary uses of established techniques, not standalone priority
claims. A specialized equivalent result may exist in different Wronskian,
orthogonal-polynomial, or symmetric-function notation. Targeted searches
for combinations of Catalan Hankel determinants, cyclotomic specialization,
repeated roots, minimal recurrences, and Wronskians included searches that
returned unrelated results. Such search failures do not establish absence
from the literature. Independent expert review and a broader priority audit
are still appropriate.

The manuscript's claims are proved in ordinary characteristic-zero
mathematics. There was no Lean formalization or proof-assistant run.
The included 22,124 successful exact assertions are finite supporting checks,
not a universal proof. The research agenda distinguishes further tasks from
the theorems actually established.
