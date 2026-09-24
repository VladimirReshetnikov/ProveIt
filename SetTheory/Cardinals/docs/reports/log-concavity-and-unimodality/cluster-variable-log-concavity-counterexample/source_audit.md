# Source and claim audit

Research date: 19 September 2026.

## Target statement

Kang, Lee, and Lim, *Unimodality and Cluster Algebras from Surfaces*.

- Examined text: arXiv:2508.04396v3.
- arXiv submission-history date for v3: 11 February 2026.
- Metadata: https://arxiv.org/abs/2508.04396
- Versioned text: https://arxiv.org/html/2508.04396v3
- Versioned PDF: https://arxiv.org/pdf/2508.04396v3
- Definition 2: extended-matrix and geometric-seed mutation.
- Section 2.2: allowed marked surfaces; the unpunctured annulus used here is
  not one of the excluded cases.
- Definition 10: a single lamination consists of exactly one allowed curve.
- Definition 12: one frozen row per constituent lamination, populated by its
  shear coordinates.
- Definition 20 (PDF p. 22): c-polynomial specialization.
- Theorem 14 (PDF p. 23): the general unpunctured-surface unimodality statement.
- Conjecture 1 (PDF p. 25): the single-lamination log-concavity statement.

The PDF pages containing the specialization definition and conjecture were
visually inspected in addition to reading their parsed text. The published
paper's example polynomials are not used as certificates or as the basis of
this disproof; our example is computed independently from standard mutation.

The arXiv record lists a related European Journal of Combinatorics publication,
volume 136 (2026), article 104392, DOI 10.1016/j.ejc.2026.104392. Attempts to
inspect the publisher page did not provide the full final text. This package
therefore targets v3 explicitly and makes no statement that the final journal
version is word-for-word identical.

Targeted searches for the title with “correction” and for the arXiv identifier
with “counterexample” did not locate an applicable correction. This is not an
exhaustive priority search and does not certify that no one else has noticed
the example. No manuscript was submitted, and no author or referee was contacted.

## Geometric foundation

Fomin and Thurston, *Cluster algebras and triangulated surfaces. Part II:
Lambda lengths*, Memoirs AMS 255 (2018), no. 1223.

- https://arxiv.org/abs/1210.5569
- https://arxiv.org/html/1210.5569
- Definition 12.5: extended matrix from shear rows.
- Theorem 12.6: matrix mutation under ordinary flips with a fixed lamination.
- Theorem 13.5: the corresponding tagged-flip statement.
- Definition 17.2: the elementary lamination is a single curve.
- Proposition 17.3: elementary laminations give principal coefficients, so
  the curve for the first arc gives shear row (1, 0) in the rank-two case.

The elementary-curve diagram on printed p. 83 (PDF page index 88) was also
visually checked. The connectedness argument in the manuscript uses that
specific elementary curve and then keeps it fixed while flipping. It does
not rely solely on the general bijection between integer shear vectors and
integral laminations, since that bijection alone says nothing about the number
of connected components.

Fomin, Shapiro, and Thurston, *Cluster algebras and triangulated surfaces. I.
Cluster complexes*, Acta Mathematica 201 (2008), 83–146:
https://arxiv.org/abs/math/0608367

Fomin and Zelevinsky, *Cluster algebras. I. Foundations*, JAMS 15 (2002), 497–529:
https://arxiv.org/abs/math/0104151

The manuscript also spells out the exchange rules and the two-triangle annulus
construction, so the algebraic certificate is directly auditable.

## OEIS identification

https://oeis.org/A001519

The entry defines a(0) = a(1) = 1 and a(n) = 3 a(n-1) - a(n-2).
These are exactly the row sums P_n^(d)(1), with no indexing shift. For n >= 1
they equal F_(2n-1). Only this established sequence identification is used;
other comments in the entry are not needed by the proof.

## What was actually verified

The source-based geometric input and the algebraic argument are distinguished:

1. The one-component, unit-weight lamination is justified in the article from
   the elementary-curve construction and the fixed-lamination flip theorem.
2. All finite matrices, polynomial recurrences, divisions, and listed
   coefficient formulas are checked with exact integers by `verify.py`.
3. The infinite statements and asymptotics have written proofs. They are not
   inferred merely from the finite test ranges.
4. No Lean proof, external CAS certification, or independent peer review is
   represented as having occurred.
5. No originality claim is made for the scalar Fibonacci sequence or the
   general techniques of linearization and transfer matrices.
