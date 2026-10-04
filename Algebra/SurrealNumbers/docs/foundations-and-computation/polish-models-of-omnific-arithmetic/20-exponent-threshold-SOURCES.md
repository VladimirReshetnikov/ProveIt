# Source provenance and scope

Access date: 4 October 2026.

## Public primary mathematical sources

**Elliot Glazer, A Topological Tennenbaum Theorem**
- https://arxiv.org/abs/2311.13699
- https://arxiv.org/pdf/2311.13699
- The displayed record had v1, submitted 22 November 2023.
- The full eight-page mathematical text was read, with the final page also
  inspected as an image. The distinction between Corollary 1 (addition under
  open induction) and Theorem 2 (the two-operation arithmetic result) was
  retained. The source of the fusion/zero-one strategy is credited.

**Andreas Blass, A partition theorem for perfect sets**
- Proceedings of the American Mathematical Society 82 (1981), 271-277.
- https://people.math.wisc.edu/~awmille1/old/m873-03/blass.pdf
- The scan's printed pages 271-272 were inspected as images. The n=2
  perfect-set partition result and the Borel/Baire extension supply the
  order-homogenization input.

**Ali Enayat, Joel David Hamkins, and Bartosz Wcislo, Topological models of arithmetic**
- https://arxiv.org/abs/1808.01270
- Fundamenta Mathematicae 256 (2022), no. 2, 171-193.
- Abstract and bibliographic record inspected for historical context. The
  historical preprint's open-question wording is not treated as current.

**Alexander S. Kechris, Classical Descriptive Set Theory**
- Graduate Texts in Mathematics 156, Springer, 1995.
- Standard reference for the explicit descriptive-set-theoretic inputs.
  The complete monograph was not read in this session. No specific page or
  theorem number is asserted without verification.

The user-provided professional-profile page could not be retrieved in full.
The chosen research connection is based on Glazer's authored mathematical
paper, not on an assumed current job title or a speculative personal profile.

## ProveIt snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned tree revision:
`9fe62865dc30d71256183466b744b98ebf7e64d6`

Pinned root:
https://github.com/VladimirReshetnikov/ProveIt/tree/9fe62865dc30d71256183466b744b98ebf7e64d6

### Inspected files

1. `README.md`, first 200 lines, initially on the default branch.
   Blob returned: `577b7ab6f2772f96da361140c3a586b6db48b384`.
   Used for repository orientation and the distinction between formal code
   and unformalized research reports, not as a proof of the new mathematics.

2. `Algebra/SurrealNumbers/docs/README.md`, pinned revision, first 170 lines.
   Blob: `adfd006467ec4f8ec9e92585e393739c6e5e7c37`.
   Used for the surreal/omnific program, report provenance and audit scope.

3. `Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/README.md`,
   pinned revision; opening material and contiguous relevant ranges 190-420
   and 400-570.
   Blob: `3c4153b2f7e29741b71a83be79eed232366367df`.
   Important catalogue entries:
   - Theorem 38.1: continuous polynomial-cone construction (credited as prior).
   - Theorem 38.2: open-induction failure in the polynomial cone.
   - Theorem 23.2 and Section 42: rational-exponent versus integer-exponent
     boundary motivating the present classification.
   - The report's separate discussion of signed-ring group topologies.
   - Its limitations and its unreviewed, explicitly claimed reverse-mathematical
     extension, which this manuscript does not use or certify.
   The full 349-page merged report was NOT read or independently audited.

4. `Algebra/SurrealNumbers/Surreal/Foundations/OmnificFloor.lean`,
   pinned revision, lines 1-150.
   Blob: `d332b117ae170b1eebff1982d9cf567ecf4915fe`.
   Read the positive-growth truncation, infinitesimal tail, sign-sensitive
   floor correction, `omnificFloor_spec`, and
   `existsUnique_omnific_integerPart`.
   No fresh Lean build was run; source inspection is not a kernel audit.

GitHub code-search results sometimes referred to an indexed commit different
from the pinned snapshot. The named source files above were explicitly fetched
at the pin where stated; search snippets were not silently treated as pinned
full-file reads. No user repository was modified.

## Priority limits

Searches were targeted, not exhaustive. Some narrowly phrased web queries
returned irrelevant results and were not used as evidence. The manuscript
therefore distinguishes mathematical proofs from the separate question of
whether their statements or variants have previously appeared in the
literature or in an unread repository manuscript.

No original claim is made for Galvin/Blass perfect-set tools, Glazer's proof
strategy, the positive polynomial-cone construction, general series arithmetic,
or the existing omnific-floor infrastructure. The proposed main extensions
are the real-exponent-subgroup classification and the one-root arithmetic
weakening.
