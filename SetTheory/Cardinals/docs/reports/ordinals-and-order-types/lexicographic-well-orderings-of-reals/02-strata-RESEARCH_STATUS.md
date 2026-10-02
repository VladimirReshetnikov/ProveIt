# Research status and source provenance

## Status

This is a research synthesis with complete written proofs of the stated results.
It has not been independently refereed or formally checked by a proof assistant.
Historical priority for the classification and absorption results is not claimed.
The proposed research questions are not represented as a verified catalog of
published open problems.

The finite test suite completed 552,450 checks successfully. These finite tests
check implementations and finite special cases only; they cannot establish the
transfinite fusion, cardinal induction, or successor-cardinal chain theorems.

The PDF was compiled from the supplied TeX and visually inspected after rendering.
The user's GitHub repository was read, not modified.

## Principal sources consulted on 2 October 2026

1. V. Kanovei and S. Shelah, *A definable nonstandard model of the reals*,
   J. Symbolic Logic 69 (2004), 159–164.
   https://arxiv.org/abs/math/0311165
   https://shelah.logic.at/papers/825/
   DOI: 10.2178/jsl/1080938834.
   The index definition and lexicographic rule were checked directly in the PDF.

2. ProveIt, *Every ordinal as a point-separating game value*, dated 20 September 2026.
   Inspected commit: 6ea60e3677bd847a00baf023c3c532c83884530e.
   File:
   SetTheory/Cardinals/docs/reports/ordinals-and-order-types/games-on-ordinals/point-separating-game-values/ordinal_separation.tex
   Only the elementary binary-cylinder perspective is reused, and the required
   argument is reproved. No compact-T1 game-realization theorem from that report
   is a premise of the present article.

3. V. Knoblauch, *Lexicographic preference representation: Intrinsic length of
   linear orders on infinite sets*, J. Mathematical Economics 105 (2023), 102823.
   DOI: 10.1016/j.jmateco.2023.102823.
   https://vickiknoblauch.com/research.html
   Used for related terminology and bibliographic context, not as an uninspected
   source of any specific theorem.

4. F. S. Herzberg, V. Kanovei, M. G. Katz, and V. Lyubetsky,
   *Minimal axiomatic frameworks for definable hyperreals with transfer*,
   J. Symbolic Logic 83 (2018), 385–391.
   https://arxiv.org/abs/1707.00202
   DOI: 10.1017/jsl.2017.48.
   Used to motivate the weak-choice research direction; no equivalence between
   that paper's choice hypotheses and this article's proofs is asserted.

## Important distinctions

- The literal full well-ordering space is not the fixed-length ultrafilter index.
- Equimorphism is not isomorphism.
- Order embeddings need not be continuous in the order topologies.
- Ordinal multiplication and addition are not cardinal arithmetic.
- A definable collection of all presentations does not choose one presentation.
- The order of the index is not the order of the resulting hyperreal field.
- Every fixed-stratum embedding comparison is settled in this manuscript, but
  a general intrinsic criterion for arbitrary orders embedding into full W is not.
- Equal invariants for W and its Dedekind completion do not prove completion absorption.
