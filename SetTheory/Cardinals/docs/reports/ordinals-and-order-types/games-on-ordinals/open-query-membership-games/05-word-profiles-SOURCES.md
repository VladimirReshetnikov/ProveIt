# Source audit and claim boundaries

Date: 30 September 2026.

## Repository source

Repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit:

    781594d886f8dc56069221e2b56bd1e94d9c6e5f

Report directory:

    SetTheory/Cardinals/docs/reports/ordinals-and-order-types/
    games-on-ordinals/open-query-membership-games/

Article Git blob:

    d1e50fd006a8ba1fe645b41b4fb37ee35f7043fe

README Git blob:

    465cb1e0629201ff5b4a17565daa8c9da4705980

The source was read through the connected GitHub tool. No claim is made that
the pin is the final repository state for the day, or that later commits leave
the same question open.

Inspected ranges in `article.tex` include:

- 1100–1520: original finite-poset discussion and finite-output provenance.
- 1720–2050: chain profiles, compact word realizations, universal-word lemma,
  and the finite-height upper-bound statement and construction.
- 2470–2570: finite-poset obstruction and finite-Hausdorff-witness distinction.
- 2690–2820: Part II Research question 1 and the later notes re-scoping it.
- 3920–4110: Part III extremal graph and ultrafilter-threshold context; none
  of its graph results is a proof dependency of the new attainment theorem.
- 4240–4390: verification status and Part III Research questions 11 and 12.
- 4570–4759: reproducibility notes and bibliography.

Some large connector responses were truncated at the output boundary; claims
were restricted to returned text. The complete paragraphs stating the target
question and its status were returned in the 4240–4390 range. README lines
210–400 were also read and provide a separate status summary.

## Exact target

Part III, Section 41, Research question 12 is titled “Compact and first-countable
finite-height spaces.” It asks whether the layer upper bound (q−1)h+s is
attained at all finite heights under compactness or first-countability
hypotheses; its preceding work proves the relevant regular-point result at
h=1, not at larger heights.

Part II, Section 27, Research question 1 asks more broadly for local conditions
ensuring attainment and for accumulating word-profile invariants. The present
article answers its extremal-attainment aspect for rank-accessible spaces,
including locally compact and sequential Hausdorff spaces, and permits infinite
terminal derivatives. It does not give a general classifier for arbitrary
fixed colorings.

Part III Research question 11, concerning arbitrary height-two local profile
data, remains open in the present work. Its solution is not implied by our
construction of a particular maximally complicated coloring.

## Existing results credited rather than claimed

- Part II Theorem 16.2: tree–layer normal form and ceiling-logarithm depth.
- Part II Theorem 19.1: restricted-start universal-word constant.
- Part II Theorem 20.1: numerical finite-height upper bound.
- Part II Theorem 20.3: exact values for specified convergent towers.
- Part III Corollary 36.2: first-countable/locally compact regular-point
  consequence within its finite-first-derivative setting.

The new article reproves the required normal form and word constant. Its full
upper-profile theorem strengthens the numerical bound and is proved directly.
The derivative calculus for finite products is elementary background and is
not presented as a historical novelty.

## New results proposed relative to this snapshot

1. Universal upper-profile theorem for every finite-height Hausdorff space.
2. Rooted forcing via predecessor-rank sequences, without whole-component
   neighborhood assumptions.
3. All-finite-height universal-profile attainment for rank-accessible spaces.
4. Countably supported extremizers and countable full-profile witnesses.
5. Extension of an arbitrary prescribed terminal coloring to such an extremizer,
   with countably many exceptional lower-rank points.
6. Exact finite-product and bounded-height sum invariants on that class.
7. Complete layer-spectrum coincidence classification, exact finite query-
   spectrum equivalence test, and dyadic aliasing families.

Each has a written proof. Items 6 and 7 are consequences of the central
attainment result and explicit arithmetic, not separate claimed solutions of
longstanding published conjectures.

## External primary sources inspected

### Chiozini–Csernák–Soukup

Lucas Chiozini, Tamás Csernák, Lajos Soukup,
“Gamification of the T0-pseudoweight via cut-and-choose games on topological
spaces,” arXiv:2510.05754v3, revised 29 May 2026.

https://arxiv.org/abs/2510.05754v3
https://arxiv.org/html/2510.05754v3
https://arxiv.org/pdf/2510.05754v3

The abstract record uses the shorter title “Cut-and-choose games in topological
spaces.” Version-specific HTML and PDF were read. PDF pages 2 and 5 (printed
page numbers) were inspected as images to confirm Definition 1.1 and Problems
1.3/1.4. This source gives game context. The new target is the repository's
Research question 12, not an unqualified claim to solve the original paper's
remaining transfinite problems.

### Borlido–Gehrke–Krebs–Straubing

Célia Borlido, Mai Gehrke, Andreas Krebs, Howard Straubing,
“Difference hierarchies and duality with an application to formal languages,”
arXiv:1812.01921 (2018).

https://arxiv.org/abs/1812.01921

The primary abstract was inspected for the established difference-chain
context. No technical theorem from this source is imported without proof.
The full partition-hierarchy literature was not exhaustively audited.

## Novelty and verification limits

Targeted web searches used combinations of open-query games, finite
Cantor–Bendixson height, sequential spaces, and set-membership games. Results
were often irrelevant. This search does not certify historical priority.
A final connected GitHub search for the exact term `rank-accessible` returned
no indexed matches in ProveIt; that is a limited search observation, not an
absence or priority proof.

The article makes a concrete claim relative to the pinned repository gap,
not a priority claim against all published or unpublished work.

No independent referee or proof assistant checked the infinite-space proofs.
The Python program only checks finite combinatorics and integer formulas.
No finite computation is represented as verification of a convergent sequence,
local compactness, sequentiality, or an arbitrary topology.

The final PDF was compiled locally, checked for undefined references and box
warnings, rendered, and visually inspected. No existing repository file was
modified by this task.
