# Targeted source audit

Date: 3 October 2026.
Repository: https://github.com/VladimirReshetnikov/ProveIt
Pinned revision: 7ff7736ecf3a0adc8536b2d083cf819e1ba39ace

## Repository sources inspected

1. Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/article.tex
2. Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md
3. Algebra/SurrealNumbers/Surreal/Foundations/SignSequence.lean
4. Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceCut.lean

The source article contains continuation material beyond the original
merged manuscripts. No current compiled page count is inferred from the
README's historical description. This audit is not a complete review of
all repository proofs, and no repository build or modification was made.

The actual sign-sequence interfaces read include universe-indexed
birthdays, first-disagreement order, small bounded fragments, non-smallness
of the full carrier, and exact-birthday small-cut separation.

## Prior Library continuations consulted

- Surreal_Well_Orders_Further_Study.tex: cut reconstruction, prefix
  nonrigidity, and the minimal-extra-structure question.
- surreal_well_orders_II.pdf: exact represented-cut extension criterion
  (Theorem 10.1), its uniform decoder, and the earlier nonextension result.
- Surreal_Lexicographic_Orders_Residual_Geometry.tex: recovery of heights
  from unranked cylinders, coverage using labels, and the unresolved
  question whether labels can be discarded.
- article(20261003-193743).tex: termination conventions, increasing-word
  obstructions, and raw class-order condensation.

These were consulted by targeted retrieval, not independently reviewed
in their entirety. They are cited as unpublished research manuscripts.

## Primary literature checked

Kanovei--Shelah, A definable nonstandard model of the reals:
https://arxiv.org/abs/math/0311165
Its indexing maps need not be injective and have ultrafilter ranges.

Ehrlich, The absolute arithmetic continuum and the unification of all
numbers great and small, BSL 18 (2012), 1--45:
https://doi.org/10.2178/bsl/1327328438
Used for historical context, not as a source for the new theorems.

Hamkins, Transfinite recursion as a fundamental principle in set theory:
https://jdh.hamkins.org/transfinite-recursion-as-a-fundamental-principle-in-set-theory/

Gitman--Hamkins, Open determinacy for class games:
https://arxiv.org/abs/1509.01099

Gitman--Hamkins--Holy--Schlicht--Williams, The exact strength of the
class forcing theorem:
https://arxiv.org/abs/1707.03700
https://doi.org/10.1017/jsl.2019.89

The literature checks support attribution and foundational distinctions.
They are not an exhaustive novelty search. New results are supported by
the proofs in the delivered manuscript.
