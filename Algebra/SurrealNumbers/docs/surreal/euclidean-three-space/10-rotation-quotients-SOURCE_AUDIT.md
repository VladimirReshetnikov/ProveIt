# Source and novelty audit

Date: 22 September 2026.

## Fixed repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal
Commit: `465a54b479a1ee842cbf7db1689a7d2f6bfe25e1`

The repository was read through the connected GitHub tools. A local clone was
not available because the container's network resolution failed. The manuscript
does not depend on a successful clone or on a local Lean build.

### Relevant material actually inspected

- Root `README.md` and the catalogue in `docs/README.md`.
- `docs/surreal/euclidean-three-space/README.md`, including its theorem inventory,
  provenance, and explicit limitations.
- Relevant source excerpts of
  `docs/surreal/euclidean-three-space/article.tex`: title and scope, quaternion
  and conjugacy sections, the infinitesimal kernel, unique divisibility, and the
  commutator-width-one proof. In particular, source lines 2650-2780 and
  2830-3030 were retrieved at the pinned commit.
- `docs/surcomplex/trigonometry/README.md`, including the exact statement of
  Theorem 4.2 and the inventory for the new rotation-group section.
- The `docs/new` listing contained only its procedural README at this snapshot;
  this was not treated as an additional mathematical manuscript.

This was a targeted comparison, not a line-by-line audit of every report or every
Lean module. The entire 71-page rotation report was not read. The trigonometry
article's theorem inventory was read through its README; the new article
recalls the infinitesimal logarithmic argument used for its circle counterexample.

## Established results not claimed as new

The rotation report already establishes the spin model, the standard-part split
extension, unique divisibility, commutator width one of the whole infinitesimal
kernel, and the valuation-graded cross product. Its proof of the single
commutator theorem already contains the unequal-axis-parameter scalar identity.

The present article starts from that identity and develops the exact mixed-cut
image. It does not claim the quaternion identity or the unrestricted
commutator-width-one conclusion as a new result.

Published precedents inspected:

1. Alessandro D'Andrea and Andrea Maffei, *Commutators of small elements in compact
   semisimple groups and Lie algebras*, Journal of Lie Theory 26 (2016), 683-690.
   Primary PDF: https://www.heldermann-verlag.de/jlt/jlt26/andla2e.pdf
   Theorem 2.5 gives local openness of the group commutator map. The relevant
   page was also inspected as a PDF image.
2. Martin Bays and Ya'acov Peterzil, *Definability in the group of infinitesimals
   of a compact Lie group*, Confluentes Mathematici 11 (2019), no. 2, 3-23.
   DOI: https://doi.org/10.5802/cml.58
   Primary PDF: https://cml.centre-mersenne.org/item/10.5802/cml.58.pdf
   The proof of Claim 3.3 explicitly records the single-commutator assertion for
   the infinitesimal SO(3) group. Theorem 1.1 recovers a valued field with
   parameters, a stronger logical conclusion than merely recovering its value
   group. The relevant commutator page was visually inspected.
3. Olivier Bournez and Quentin Guilmant, *Surreal fields stable under exponential
   and logarithmic functions*, arXiv:2201.08199v1 (2022).
   https://arxiv.org/abs/2201.08199
   The field, Hahn, normal-form, and coefficientwise addition background was
   checked in Sections 2.2-2.3, including Corollary 2.1 and Theorem 2.6.

Broader searches for normal-subgroup and surreal-quotient terminology were
inconclusive. Unrelated search hits were not used as evidence. General papers on
orthogonal groups over rings were surfaced, but no claim about their detailed
scope or non-applicability is made without a content check.

## Candidate contributions and conservative novelty assessment

- Exact single-commutator images at two prescribed lower bounds, and their
  arbitrary-upper-segment form: a direct but useful refinement of the existing
  quaternion construction.
- Normal closure of an infinitesimal element and the resulting classification
  of ambient-normal subgroups: proved from finite algebra here, but general
  historical priority is not asserted.
- Classification of perfect cut subgroups; exact lower-central/derived series;
  identification of the stage-omega perfect residual: consequences of the cut
  calculus, with full proofs.
- Recovery of value arithmetic from compact elements of the ambient normal
  lattice: an explicit description, not a first discovery of valued-field
  recoverability.
- Universal set-sized quotient of the full surreal rotation group, its set-action
  consequences, and its SO(n)/SU(n) extensions: the main candidate-original
  surreal-specific result. No identical formulation was located in the sources
  inspected, but this is not an exhaustive priority certification.
- The circle/U(n) counterexample: a consequence of established torus splitting
  and coefficient extraction, included to show a genuine boundary rather than
  offered as an independent discovery.

## Verification boundary

39 named finite checks passed in SymPy. No Lean build, theorem-prover proof,
independent referee review, or verification of all statements in the cited
repository has been performed. The main theorem does not require trusting a
new analytic conjecture: its proof uses the finite lemmas in the article plus
standard surreal real-closedness, monomials, and the set/class size argument.
