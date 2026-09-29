# Proof audit

## Status

All mathematical results claimed in the manuscript have written proofs.
Basic oracle-computability facts, jump monotonicity and strictness, and the
Baire category theorem are standard background. No unproved new construction
from the repository is assumed. There is no Lean file or machine-checked proof.
The finite Python tests are supporting checks, not proof certificates for the
infinitary theorems.

## Dependency chain

1. Finite density estimates and the prefix-density metric give completeness of
   the density-zero class and continuity of finite oracle computations.
2. Baire category plus the local decoder gives robust radius (Theorem 3.1).
   This is a form of the published cone-avoiding compactness theorem, not a new
   compactness principle.
3. Positive-density columns, their uniformly small tails, and robust coding
   give the lower inclusion for ideal realization; robust radius gives the
   reverse inclusion (Theorem 5.1).
4. The stronger repeated robust code supplies a uniform array converging by
   whole rows; finite-head/small-tail assembly gives the converse spectrum
   calculation (Theorem 6.2).
5. The relativized limit lemma gives the classical dyadic jump spectrum.
6. Robust radius and computable density approximation prove neutral joins;
   spectrum intersection then gives the exact filter (Theorems 8.2 and 8.4).
7. Uniform transport of dyadic codes gives the forward embedding. Relative
   Friedberg inversion supplies the separating degree for the converse
   (Theorem 9.2).
8. Explicit strict extensions and a diagonal jump above a countable join give
   the two assertions of Corollary 9.4.

## Quantifiers and nonuniform choices

- The row condition is `forall i, exists s_i, forall s >= s_i, forall n`.
  It is not `forall i,n, exists s_(i,n), forall s >= s_(i,n)`.
- The uniform decoder returns the full array, not a uniformly selected
  stabilized row.
- A fixed finite patch can be included in a Turing program. There is no claim
  that its length or bits can be found effectively from an arbitrary oracle.
- The finite-column approximants to a dyadic code are individually computable;
  their program indices need not form a computable sequence.
- A countable ideal is realized from a presentation; no computable enumeration
  of an arbitrary ideal is inferred from its countability.

## Coding checks

- `p(i,m) = 2^i(2m+1)-1` partitions all nonnegative integers, including 0.
- The tail over columns i >= k has exactly floor(N/2^k) points below N.
- A wrong block majority forces error fraction at least 1/4 at the end of
  the block. Ties are resolved as 0 throughout.
- `E(A)=J(R(A))`, not merely `R(A)`, is used for whole-real recovery.
- Assembly from finitely many errors in each column uses a finite head and a
  tail of density at most 2^(-k); arbitrary countable unions of null sets are
  never assumed null.
- The exact code recovers A_i(n) at p(i, 2^(p(n,0))). This is computable, not
  claimed to be computationally efficient.

## Order-theoretic checks

- Nonuniform coarse reducibility corresponds to REVERSED spectrum inclusion.
- The common lower cone of the spectrum is the core.
- A spectrum has an infimum iff its core is principal; the infimum need not
  belong to the spectrum.
- Relative jump inversion supplies BOTH B >=_T X and B' equivalent_T K.
- The upper-cone embedding does not necessarily map its bottom to [X].
- The image is closed under binary coarse joins. The full fixed-core fiber is
  not claimed to be closed under arbitrary such joins.
- No maximal coarse degree in a fiber and no countable cofinal family in a
  fiber are proved separately. Neither assertion is substituted for a theorem
  about minimal solving Turing degrees.

## Literature and novelty

The ideal-column mechanism is already present in HJS (2021), Theorem 3.11.
The robust-radius input is HJKS (2016), Theorem 3.7. The dyadic spectrum is the
relativized JS (2012), Theorem 2.19 criterion. The research contribution is the
specified repository-target resolution and the exact structural extensions
proved in the manuscript. No verified global-priority claim is made.

## Remaining review targets

Independent checking of the full arguments, especially the whole-row
uniformity distinction and the converse fixed-core embedding, remains
valuable. No unacknowledged gap is intentionally left as an assumption, but
written proofs and finite tests are not substitutes for independent refereeing
or formal verification.
