# Targeted source audit

Date: 3 October 2026.
Pinned ProveIt revision: `109aaca1505c12d70ae169bdc2011f40bd476f7d`.
A later branch query returned `d5bd4a67b41b89688a079997574a94bcd855bb83`, with
the pinned revision among its parents. The manuscript intentionally stays
with the inspected pin.

## Repository inputs

Repository: https://github.com/VladimirReshetnikov/ProveIt

The GitHub connector was used to inspect:

1. `Algebra/SurrealNumbers/docs/README.md`, opening guide and report scope.
2. `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md`,
   coverage, prior-result provenance, foundational conventions, and formal status.
3. `Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceCut.lean`, including
   `exists_cut_separator_of_birthday_lt` and `small_cut_fillers`.
4. `Algebra/SurrealNumbers/Surreal/Foundations/SmallCutData.lean`, including
   reindexing, `ofSmallSets`, and the explicitly small separator interface.
5. Search results and cross-references for the companion reals report.

The recursive repository tree output was too large to audit exhaustively.
The main merged report's entire TeX and every proof were not reviewed. The
article does not claim that they were. No repository modification or full
build was attempted through the connector.

## Earlier manuscripts in the user's Library

`Surreal_Well_Orders_Further_Study.pdf` / matching TeX:
*Lexicographic Orders of Surreal Well-Orderings: Cut Reconstruction,
Asymmetric Products, Prefix Non-Rigidity, and Size-Safe Foundations*,
3 October 2026. Its exact Question 15.9 (termination cuts) and Question 15.11
(residual iteration) motivated this continuation. Its abstract and research
agenda were read through Files; all of its other proofs were not audited.

`surreal_well_orders_II.pdf`:
*Lexicographic Well-Orders of the Surreal Numbers, II: Exact Cut Spectra,
Branch Recognition, Optimal Support Reserves, and Automorphism-Extension
Obstructions*, 3 October 2026. Its scope was checked to avoid presenting
previous continuation topics as new. It is not a proof dependency.

## Primary literature

- Kanovei and Shelah, arXiv:math/0311165, and the author's Sh:825 publication
  record. The actual index definition was inspected in the PDF on page 2:
  maps from the continuum cardinal to P(N), whose range is an ultrafilter.
  https://arxiv.org/abs/math/0311165
  https://shelah.logic.at/papers/825/
- Hamkins's author explanation of the global-choice universality argument:
  https://mathoverflow.net/questions/227849/is-the-universality-of-the-surreal-number-line-a-weak-global-choice-principle
  Some direct requests failed, but exact-title search returned the author
  text and date. No converse to global-choice universality is inferred.
- Gitman and Hamkins, *Open determinacy for class games*:
  https://arxiv.org/abs/1509.01099
- Gitman, Hamkins, Holy, Schlicht, and Williams, *The exact strength of the
  class forcing theorem*:
  https://arxiv.org/abs/1707.03700
- Brown and Suarez, *Algebraic structures arising from the finite condensation
  on linear orders*, arXiv:2505.01936v4, 16 September 2025:
  https://arxiv.org/abs/2505.01936

These are targeted references for context, attribution, and proof-strength
boundaries. The literature search is not exhaustive and cannot establish
historical priority of the new formulations.
