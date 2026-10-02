# Source and novelty ledger

Consulted October 2, 2026. This is a targeted audit, not an exhaustive survey.
The bibliography in `article.tex` is the article's primary reference list.

## Pinned ProveIt revision

`928ea97017a25ebe56d240c84f27d2275d818c75`

Repository files were read through the GitHub connector, not inferred from
repository names or an earlier conversation.

1. MRDP specification and proof-chain guide:
   https://github.com/VladimirReshetnikov/ProveIt/blob/928ea97017a25ebe56d240c84f27d2275d818c75/Computability/HilbertTenthProblem/Lean/MRDP.md
   Specifies one natural input, a fixed finite tuple of natural witnesses,
   integer coefficients, and no supplied numerical complexity bound. The paper
   explains the polynomial pairing needed for a two-parameter universal relation.
2. Hilbert-tenth README:
   https://github.com/VladimirReshetnikov/ProveIt/blob/928ea97017a25ebe56d240c84f27d2275d818c75/Computability/HilbertTenthProblem/README.md
   Reports separate 75-operation certificate and 87-operation universal-polynomial
   bounds. These are repository claims at that revision, not independently rebuilt
   bounds or quantities improved by this package.
3. Neighboring canonical routing / RLE source ledger:
   https://github.com/VladimirReshetnikov/ProveIt/blob/928ea97017a25ebe56d240c84f27d2275d818c75/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/12-rle-routing-SOURCES.md
   Distinguishes finite periodic routing from Cairns's infinite sandpile model.
   The present compiler uses support-burning rather than last-used routing edges.

## Primary literature

1. Antal A. Járai, *Sandpile models*, arXiv:1401.0354v3, September 13, 2018.
   https://arxiv.org/abs/1401.0354
   https://arxiv.org/pdf/1401.0354
   Finite-graph theory and Section 4.1 burning/ample configurations. The
   first-to-finish toppling argument is a classical ingredient. The title page
   and relevant PDF content were inspected; the compiler formulas are not
   attributed to that survey.
2. Hannah Cairns, *Some halting problems for abelian sandpiles are undecidable
   in dimension three*, arXiv:1508.00161v2, March 24, 2021.
   https://arxiv.org/abs/1508.00161
   https://arxiv.org/html/1508.00161v2
   Definitions of local/global halting, periodic-plus-finite input descriptions,
   and Sections 5–6 / Theorem 3. The imported reduction concerns finitely many
   total topplings. Merely finitely many topplings at each vertex is a different
   predicate. The planar questions are attributed to this version, not claimed
   to have had an exhaustive 2026 status audit.
3. Tobias Friedrich and Lionel Levine, *Fast simulation of large-scale growth
   models*, Random Structures & Algorithms 42 (2013), 185–213;
   arXiv:1006.1003v2.
   https://arxiv.org/abs/1006.1003
   https://lionellevine.github.io/
   Prior odometer/least-action validation and computation without all intermediate
   states. Publication details are also listed on the author's publication page.
4. Yuri Matiyasevich, *Towards finite-fold Diophantine representations*,
   Journal of Mathematical Sciences 171(6) (2010), 745–752.
   DOI: 10.1007/s10958-010-0179-4.
   https://www.mathnet.ru/eng/znsl3816
   Distinguishes ordinary Diophantine representation from multiplicity-sensitive
   representation. The article's equivalence theorem is proved directly; it does
   not claim a resolution of either representation principle.
5. Jonas Bayer and Marco David, *A Formal Proof of Complexity Bounds on
   Diophantine Equations*, ITP 2025, LIPIcs 352, article 3.
   DOI: 10.4230/LIPIcs.ITP.2025.3.
   https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.3
   Formalization context, not a verification of the new sandpile construction.

## Dependency and novelty boundary

- Self-contained in the manuscript: finite termination/least action, exact
  support criterion, canonical local ranks, both cubic compilers and all
  auxiliary uniqueness claims, inverse zero-set maps, collar/canonical-radius
  interface, quadratic spatial witness bounds, explicit eventual period theorem.
- Imported for the universal application: Cairns's effective simulation and
  ordinary MRDP. The absence of a computable radius bound is a consequence of
  that simulation together with the proved finite spatial test.
- Not supplied: fixed-arity compression of the spatial family with preserved
  multiplicity; a numerical universal sandpile polynomial; a formalized Cairns
  loader; a Lean proof or a rerun of ProveIt's formal build.
- The proposed exact compiler may have related or equivalent predecessors.
  A targeted search and a missing exact-title match do not establish priority.
  The classical ingredients and the sandpile-group mechanism are not claimed
  as discoveries of this report.

## Artifact verification

`verification.json`, `verification_compact.json`, and `verification_spatial.json`
record the exact finite checks actually run. The Python tests supplement the
ordinary proofs; they do not establish infinite theorems by finite sampling.
The PDF was compiled with pdfLaTeX, checked for unresolved references and
layout warnings, rendered with Poppler, and visually inspected.
