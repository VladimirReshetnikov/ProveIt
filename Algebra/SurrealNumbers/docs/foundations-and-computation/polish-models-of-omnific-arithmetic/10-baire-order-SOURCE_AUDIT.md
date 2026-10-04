# Source and proof audit

## Selected intersection

The selected research connection is Glazer's topology of arithmetic and
ProveIt's Presburger and omnific ordered-algebra interfaces. This selection
is based on primary mathematical work, not an inferred complete biography
or a claim about current employment. The supplied LinkedIn profile was not
used to assert unverified personal details.

## External primary sources

1. Elliot Glazer, *A Topological Tennenbaum Theorem*, arXiv:2311.13699v1 (2023).
   https://arxiv.org/abs/2311.13699
   Full HTML: https://arxiv.org/html/2311.13699v1
   Corollary 1 concerns an uncountable Polish positive model of Q + IOpen,
   continuous addition, and Borel multiplication. Question 1 asks whether
   Theorem 2 is provable in ATR_0. Question 2 asks for an uncountable Polish
   Presburger model with continuous addition. These scopes are distinguished
   from the signed-group theorem proved in this package.

2. Ruiyuan Chen, *On the Pettis--Johnstone theorem for localic groups*,
   arXiv:2109.12721v1 (2021).
   https://arxiv.org/abs/2109.12721
   Context for the classical Pettis/category mechanism. The exact local-bound
   argument used by the manuscript is reproduced in full.

3. Alexander S. Kechris, *Dynamics of non-archimedean Polish groups*, accepted
   manuscript and Caltech bibliographic record.
   https://authors.library.caltech.edu/records/d2wb1-23129
   Used for the standard definition of a non-Archimedean group topology.
   The main theorem does not require that hypothesis.

4. S. Mohsenipour, *Discrete orderings in the real spectrum*,
   arXiv:1807.00501v2.
   https://arxiv.org/html/1807.00501v2
   Background on discretely ordered rings and weak arithmetic.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt
Inspected tree/commit: 6fef5383b126be343cccc9baf47081ef37ab5afe

Directly inspected relevant files:

- Logic/PresburgerArithmetic/README.md
  Blob: a29a6b54c98ae5dbf5e3267a96f10dc5e1514a79
  Describes affine syntax, normalization, Cooper elimination, the Lean
  sentence decision procedure, and the independent Rocq normalized step.

- Algebra/SurrealNumbers/README.md
  Blob: 4f830b663aa28748468a9382829d0e4d90e7f8ba
  Describes actual omnific-ring construction, least positivity of 1,
  bounded omnific elements being ordinary integers, and the formalization
  ledger separating checked claims from unrefereed report claims.

The repository was read with the GitHub connector. No repository files were
modified, no build was run, and unrelated advertised results were not used.

## Earlier project manuscripts inspected through the user's Library

- *Local Compactness Forces Arithmetic Rigidity* (3 October 2026).
  Source: article(20261004-024118).tex
  PDF: article(20261004-024117).pdf
  Used for the preceding lcsc theorem, its order-unit amplification,
  its examples, and its explicit remove-local-compactness question.

- *Polishability at the Hahn--Puiseux--Levi-Civita Boundary* (3 October 2026).
  Source: article(20261004-024450).tex
  PDF: article(20261004-024447).pdf
  Used for the already-developed local order bound and the distinction
  between additive topological groups and positive monoids.

These are unrefereed project documents, not external priority evidence. They
are credited rather than repackaged as new work.

## New proof dependency chain

1. Strict ordered algebra gives |a*x| = a*|x| for a > 0 and permits cancellation.
2. The map x -> a*x + H_a has kernel exactly Fin(A).
3. Discrete order gives Fin(A) = Z*1 by external induction on ordinary integers.
4. Baire group + Baire positive cone gives an order-bounded neighborhood.
5. That neighborhood makes an appropriate principal convex hull H_a open.
6. ccc makes A/H_a countable, hence A/(Z*1) and A countable.
7. A countable Hausdorff Baire group is discrete.

No measurability or continuity of multiplication appears in steps 1--7.
The self-embedding theorem uses the same kernel computation with an additive
order embedding instead of multiplication. The nonseparable cardinal result
uses an open-coset transversal and ZFC cardinal arithmetic.

## Verification status

- LaTeX compiled successfully to 23 pages, with no unresolved references or
  overfull/underfull box warnings in the final build.
- PDF pages were rendered and visually checked; page-text bounding boxes
  were also checked for out-of-page content.
- Deterministic exact rational tests passed; details in verification_results.json.
- The finite tests do not certify the main theorem.
- No Lean/Rocq kernel verification, independent referee review, or exhaustive
  bibliographic priority certification was performed.
