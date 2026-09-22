# Repository coverage audit

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned revision: `e260237db9b71da8b74a0c13c8e6355119091100`

Article date: September 21, 2026.

## Evidence inspected

1. The complete documentation map, `docs/README.md`. It lists fifteen packages
   in three families and describes their intended relationships.
   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/README.md

2. The complete detailed inventory of `docs/surcomplex/polynomial-algebra/`.
   This describes the merged report, its three source manuscripts, the
   contribution of each, and its scope limitations.
   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/polynomial-algebra/README.md

3. Opening source lines 1–210 of that report's `article.tex`, including its
   abstract, declared mathematical setting, provenance, and scope.
   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/surcomplex/polynomial-algebra/article.tex

4. Opening lines 1–170 of the foundations package's detailed README, including
   its workspace, set/class, transfer, and topology distinctions.
   https://github.com/VladimirReshetnikov/Surreal/blob/e260237db9b71da8b74a0c13c8e6355119091100/docs/foundations-and-computation/foundations/README.md

The repository tree and the available opening catalogue text in `manifest.tex`
were also consulted. No claim of a full source-by-source mathematical audit
is made. In particular, a search returning no matches was not treated as
proof that a word or topic occurs nowhere in the repository.

## Selected gap

A dedicated treatment of finite-dimensional spectral and singular-value
theory, with an explicit bridge to Hahn valuation geometry.

The polynomial-algebra inventory already includes an algebraic Schur inequality,
a differentiating compression, Hermite signatures, finite pairings, and
Newton profiles. These are adjacent matrix ingredients and are acknowledged
in the new article. The gap is their development into a systematic theory of
Hermitian geometry, SVD, rank across scales, conditioning, and spectral-subspace
stability, rather than an assertion that the repository contains no matrices.

## Avoided duplication

The new article does not retell the repository's trigonometry, analytic-germ
ring distinctions, contour/residue construction, global divisors, birthday
bounds, genetic primitives, broad foundational comparison, or general CAS
architecture. It uses the set-sized Hahn workspace convention and gives its
own short finite-data localization argument.

Its direct bridge to existing material is the Gram polynomial
`det(I+s A* A)`: positivity makes its coefficient valuations equal twice the
minimum minor valuations. This specializes root-profile information to
singular-value geometry and supplies leading-amplitude data as well.

## Attribution boundary

Real-closed-field spectral theory, SVD, low-rank approximation, pseudoinverses,
and classical perturbation theory are not presented as new discoveries.
The article's value is a rigorous integrated exposition and its explicit
non-Archimedean interpretation. The cited research sources and canonical
surreal/Hahn references are listed in the article's internal bibliography.
The article does not claim an exhaustive literature search or priority for
the determinantal/valuation consequences it proves.

## Repository changes

None. Suggested destination for a future integration is
`docs/surcomplex/spectral-theory/`, but no upload, commit, or pull request
was performed.
