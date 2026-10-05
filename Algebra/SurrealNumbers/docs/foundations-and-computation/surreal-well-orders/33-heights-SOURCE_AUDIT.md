# Source and repository audit

Access date: 4 October 2026. The audit is targeted, not exhaustive.

## User repository inspected through the GitHub connector

Repository: https://github.com/VladimirReshetnikov/ProveIt

Read:

1. `README.md`, including the repository structure and separation between
   formal proofs, admitted interfaces, and research drafts.
2. `Algebra/SurrealNumbers/docs/README.md`, the surreal report catalogue.
   Returned blob: `b7b69377ff172577b642b4fb78bfb2b09989dcd0`.
3. `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/README.md`,
   including provenance, prior class-order/condensation work, and status.
   Returned blob: `d2e24b58617bbbe56aadbbdeb11c2018da51ae79`.

The relevant guide describes 23 merged manuscripts and an 860-page PDF.
The guide calls the work unrefereed and not fully formalized. Its existing
condensation material is acknowledged. The full article was not subjected to a
line-by-line audit, and no absence-of-overlap claim is based on the guide alone.

Blob hashes identify file contents; they are not labeled as commit hashes.
Live main-branch contents can change after inspection. No repository mutation
was requested or performed.

## Primary mathematical sources consulted

- Hamkins and Woodin, *Open class determinacy is preserved by forcing*, 2018.
  https://arxiv.org/html/1806.11180v1
  Used for the class well-foundedness/recursion/comparison interface and the
  precise statement of the published comparison question.

- Gitman and Hamkins, *Open determinacy for class games*, 2015, revised 2016.
  https://arxiv.org/abs/1509.01099
  Used for the ETR, class games, and truth-predicate interface.

- Gitman, Hamkins, Holy, Schlicht, Williams, *The exact strength of the class
  forcing theorem*, JSL 85 (2020), 869-905; arXiv revision 2021.
  https://arxiv.org/abs/1707.03700
  Used to distinguish ETR_Ord from arbitrary class-length ETR.

- Williams, *The Structure of Models of Second-order Set Theories*, 2018.
  https://arxiv.org/abs/1804.09526
  Used for model realizations and unrolling; the Class Collection hypothesis
  is retained in the quoted theorem interface.

- Barton and Williams, *Varieties of Class-Theoretic Potentialism*, version 4,
  2023. https://arxiv.org/html/2108.01543v4
  Used as context for varying class resources over a fixed set model.

- Antos and Friedman, *Hyperclass Forcing in Morse-Kelley Class Theory*, 2015.
  https://arxiv.org/abs/1510.04082
  Used for the explicitly strengthened beta-model/hyperclass coding interface,
  not as a theorem about plain GBC.

- Hamkins, *Second-order transfinite recursion is equivalent to Kelley-Morse
  set theory over GBC*, 23 July 2017.
  https://jdh.hamkins.org/second-order-transfinite-recursion-is-equivalent-to-kelley-morse-set-theory/
  Used to distinguish elementary from second-order recursion.

- Official mathlib documentation, `Mathlib.SetTheory.Ordinal.Basic`.
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/SetTheory/Ordinal/Basic.html
  Used for the universe-indexed ordinal interface and the role of
  `Ordinal.type`. No implementation was compiled against this interface.

## Search limits and originality

The targeted search located the 2018 comparison question and relevant primary
literature. It did not establish a complete current resolution of all the
published open questions. No claim that every research direction in the
article is globally open is made.

The canonical-division, finite-digit, diagonal, and definability-height
arguments are written out in the article. The search did not certify their
historical novelty; an independent bibliographic and mathematical review is
needed before any priority claim or journal submission.

No third-party PDF, source archive, font file, or long copyrighted excerpt is
redistributed. The bibliography is embedded in the self-contained LaTeX file.
