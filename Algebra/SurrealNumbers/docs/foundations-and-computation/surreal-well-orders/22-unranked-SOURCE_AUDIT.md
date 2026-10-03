# Targeted source audit

Repository: VladimirReshetnikov/ProveIt
Pinned commit: d5bd4a67b41b89688a079997574a94bcd855bb83
Inspection date: 3 October 2026

## Maintained report

Directory:
Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/

The maintained README was inspected for scope, the union of four source
manuscripts, theorem inventory, review status, and formalization limitations.
It describes a 116-page report. The new article cites the maintained report
and identifies the proof mechanisms it uses; it does not certify every theorem
of the merged report or claim to have built that repository.

## Lean source read directly at the pinned revision

Algebra/SurrealNumbers/Surreal/Foundations/SignSequence.lean
Git blob: e2c093860f29b0b9ea312d50099fc4aa89a76a99

Read interface and declarations include SignSequence, lt_iff, ofSigns,
ordinalOrderEmbedding, birthdays_bounded, not_small, small_bounded,
IsPrefix, simpler_wellFounded, and truncate.

Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceCut.lean
Git blob: c5c35afd98a5ad293687367ee9fb0244f94cc91c

Read declarations include exists_cut_separator_of_birthday_lt and
small_cut_fillers, including the complete bounded Boolean-word proof route.

## Prior user-supplied continuations

- surreal_well_orders_II.tex:
  Lexicographic Well-Orders of the Surreal Numbers, II: Exact Cut Spectra,
  Branch Recognition, Optimal Support Reserves, and Automorphism-Extension
  Obstructions. Research manuscript, 3 October 2026.

- Surreal_Well_Orders_Further_Study.tex:
  Lexicographic Orders of Surreal Well-Orderings: Cut Reconstruction,
  Asymmetric Products, Prefix Non-Rigidity, and Size-Safe Foundations.
  Research manuscript, 3 October 2026.

These Library texts were consulted for their result summaries and relevant
research questions. Both reference the older repository commit
0ecd158fd163bc4aca0ee40ccf6479ca6cf5f2a8. They are credited separately and are
not assumed to have been merged into the pinned current repository.

## Primary literature

Kanovei–Shelah, A definable nonstandard model of the reals, math/0311165.
Ehrlich, The absolute arithmetic continuum and the unification of all numbers
great and small, Bulletin of Symbolic Logic 18 (2012), 1–45.
Gitman–Hamkins, Open determinacy for class games, arXiv:1509.01099.
Gitman–Hamkins–Holy–Schlicht–Williams, The exact strength of the class forcing
theorem, arXiv:1707.03700, JSL 85 (2020), 869–905.

The LaTeX bibliography provides primary-source links and distinguishes these
references from unpublished repository and user-supplied manuscripts.
