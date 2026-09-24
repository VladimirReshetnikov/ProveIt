# Source and novelty audit

## Repository pin

The GitHub commits endpoint explicitly resolved the following object as a commit:

- Repository: VladimirReshetnikov/Surreal
- Commit: `efc5446229dbf61a97bdd5edae91dba20af9d131`
- Associated tree: `aba698290ee2cd54f97db3a8b4038c010fcb47d8`
- Commit date returned by GitHub: 2026-09-23T23:35:05Z

The commit-versus-tree distinction was checked explicitly. This is a comparison
pin, not an assertion that the article's theorems occur in that commit.

## Focused repository inspection

The following material was read, in some cases through excerpts or a truncated
catalogue response rather than as a complete mathematical proof:

- Root `README.md` (opening and research/formalization material).
- `docs/README.md` (catalogue, reading routes, and relevant report descriptions).
- `docs/surreal/omnific-diophantine-geometry/README.md` (especially the detailed
  reconciliation of its support, Euler, two-ring, curve and logarithmic results).
- `docs/surreal/set-sized-quotients-of-omnific-integers/README.md`.
- `docs/surreal/omnific-preserving-automorphisms/README.md`.
- `docs/surreal/independent-surreal-copies/README.md`.
- Opening of `docs/surcomplex/holonomic-rigidity-for-entire-hahn-functions/article.tex`.

A search for an open derivation direction returned no useful matches; that
negative result is not evidence of mathematical absence. An unsuccessful guess
at a nonabelian-report path was discarded. No claim to have read the entire
repository is made.

## Antecedents credited

The support decomposition, constant extraction, and Euler/two-ring mechanism
already belong to the repository's omnific Diophantine program. The present
article proves the elementary support facts independently and does not claim
them as new. Its more specific mechanisms are the universal polynomial of
logarithmic root velocities and the characteristic polynomial of a logarithmic
derivative of an étale unit.

The classical generalized-series and omnific background is supported by:

S. L'Innocente and V. Mantova, *A factorisation theory for generalised power
series and omnific integers*, Advances in Mathematics 442 (2024), 109513,
DOI 10.1016/j.aim.2024.109513; arXiv:1710.07304v5.

Its Fact 2.1.1 states the Hahn-field algebraic/real closedness criterion.
The abstract, relevant background, and publication metadata were inspected.
Its results on factorization and Gonshor's prime example are not reproved or
claimed by the present manuscript.

The Stacks Project sections 10.143 (00U0), 10.150 (00UP), and Lemma 49.3.1
(0BJF) provide the étale, formal lifting, and discriminant foundations.
These official primary-source pages were opened and inspected.

The polynomial-parameter translation question was explicitly posed by
Math Stack Exchange user Oblomov on 25 January 2016, question 1626152.
The article gives a uniform characteristic-zero answer as a specialization,
but does not elevate that classical case into a new major conjecture.

## Novelty boundary

The arbitrary-rank Hahn discriminant theorem, the finite étale unit theorem,
and their combined arithmetic and normal-matrix consequences are offered as
proposed contributions developed for this request. No matching statement was
identified in the material inspected, but this is not an exhaustive novelty
search. A prior equivalent result may exist under different language, and
independent expert review is warranted.

The manuscript does not claim a complete finite étale classification. Its
further questions are explicitly questions not settled by this manuscript,
not a certified catalogue of previously unknown open problems.

## No transferred proof status

The repository contains checked Lean declarations for several antecedents.
That fact does not formally verify this manuscript. The finite SymPy checks
likewise do not verify arbitrary supports, all degrees, or étale lifting.
