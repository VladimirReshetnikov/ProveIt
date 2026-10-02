# Source and claim audit

Audit date: October 2, 2026.
Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot anchor: `4cccfa06866b6b81b2467e1cf7514ea85ed0216d`.

Repository sources were read through the connected GitHub interface. Searches and directory inspection established the relevant research area. This was a targeted audit, not a review of every file in the repository. The snapshot anchors are also embedded as clickable bibliography links in the article.

## Inspected source interfaces

The following first three paths are under:

    Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/

### 1. group_affine_input_obstruction.md

Blob SHA: `477a3ecec339b0f4cb12cdabe506698bd01c6cc2`.

The full note was read. The snapshot fetch also confirmed this blob hash. It proves the empty/singleton/single-coset classification for affine SL2 inputs and two independently affine SL2 blocks. Its affine SL3 example accepts `{1,2}` and disproves the single-coset classification in higher dimension. It does not prove the all-dimensional finite-or-periodic replacement developed in this report.

### 2. group_commutator_universal_substrate.md

Blob SHA at the snapshot: `1026206ee09832726f50638db4c884b15909c266`.

The sections defining the graph-group commutator encoding, effective finite-presentation interface, conjugated fibre product, faithful matrix representation, and ordinary-input quadratic loader were read. A subsequent snapshot fetch confirmed the file identity. The large response was truncated after the relevant main construction; no claim is made to have reviewed every later executable-audit paragraph.

The source already gives the quadratic universal input construction. The article reconstructs its arbitrary-finite-rank version using conjugates of one free matrix generator, so it does not need the optional two-generator-output refinement of effective Higman embedding. The upper bound is attributed to this source. The new sharp-threshold conclusion combines that existing upper bound with the all-dimensional affine lower bound.

### 3. imported_substrate_review_20261002.md

Blob SHA from the read: `8bd07142c8b4298fb636e47b40d2d84e993a40ce`.

The full review was read. It distinguishes externally bounded certificate families from fixed unbounded polynomials, and existence from witness uniqueness. It reports the 87-operation fixed universal-polynomial benchmark and explains why small matrix input loaders are not complete matrix-word certificates. The numerical benchmark is quoted as repository-reported, not independently reconstructed or beaten.

### 4. MRDPCore.lean

Full path:

    Computability/HilbertTenthProblem/Lean/Diophantine/Common/MRDPCore.lean

Blob SHA from the read: `e062e6ec76a0d47e4a7a2156b6a09aa2eee05110`.

The final `mrdp` theorem and its nearby comments were read. The theorem states that every recursively enumerable natural set has a fixed integer-coefficient polynomial representation with finitely many natural witnesses. No new Lean build was run here. The natural-to-integer witness conversion in the article uses four squares before applying the circuit compiler.

## External mathematical dependencies

- **Higman embedding:** the classical embedding theorem and its effective finite-presentation interface are imported. The official publisher record for Higman's 1961 article and the arXiv abstract/record of V. H. Mikaelian's *An explicit algorithm for the Higman Embedding Theorem* (arXiv:2507.04347) were checked. The complete algorithm was not reproduced, run, or independently formally verified. The strengthened optional two-generator output is not needed by this article's reconstruction.
- **Mihailova fibre products:** the introductory construction in Bogopolski–Ventura, arXiv:0810.0690, was checked in the paper; the article also gives its finite-generation proof. Extra hypotheses in that paper's later recursive-presentation theorem are not treated as hypotheses of the elementary fibre-product construction.
- **Free shear matrices:** a direct ping-pong argument and the independence of conjugate generators are included. Chang–Jennings–Ree (1958) is a primary literature reference for this classical matrix-group framework.
- **MRDP:** used only for the general computably enumerable corollary of the explicit compiler, not for the rigidity, period, multiplication, or compiler proofs. The repository theorem and Matiyasevich's original theorem are attributed.
- **Four-square theorem:** used to replace natural source witnesses with integer witnesses before circuit compilation. This substitution need not preserve their multiplicities.
- **Integer-valued polynomials:** Newton interpolation is reproved; Cahen–Chabert is cited for the established theory.
- **Polynomial sequences in groups:** Leibman and Hu are cited as related literature, not as sources already checked to prove the exact sharp statements here. A thorough priority audit against this literature remains a proposed research task.

## Claim provenance

| Claim | Status in this package |
|---|---|
| Affine subgroup hits are finite or exactly periodic in every dimension | Proved here as an extension of the inspected paired-SL2 result |
| Exact free basis and integer interpolation coordinates | Proved here using finite logarithms and interpolation |
| Finite bound `rank(intersection)+1`, and realization of prescribed finite sets | Proved here with Vandermonde affine independence |
| Exact quotient-exponent period `P_k(e)` and its sharpness | Proved here using binomial divisibility; exact finite tests included |
| Commuting-polynomial extension | Proved here, with explicit coefficient-commutativity hypothesis |
| Degree-two matrix subgroup universality | Existing repository construction, reconstructed with an explicit external embedding dependency |
| Degree two is sharp even with unrestricted matrix dimension | New synthesis of the proved lower bound with the attributed upper bound |
| Six-dimensional affine multiplication and circuit resource bounds | Explicit constructions and proofs here; not claims of global novelty or optimal dimension |
| All c.e. relations have existentially quantified affine abelian representations | Corollary of MRDP plus the explicit compiler, not an independent MRDP proof |
| No unrestricted uniform algorithm for extracting the finite/periodic description | Proved by reduction from fixed subgroup membership |
| One-witness decidability | Proved for the printed independent block-cyclic family only |
| 91,142 exact cases pass | Recorded executable evidence, not a proof-assistant result |

## Scope safeguards

1. Input degree, matrix dimension, witness count, polynomial degree, and full arithmetic-operation count are different resources.
2. An affine input curve has no extra quantified input coordinates. The quantified affine-pencil compiler uses many such coordinates.
3. Pointwise unipotence does not imply that normalized polynomial coefficients commute.
4. The subgroup intersection lattice exists abstractly; it is not assumed uniformly computable from an arbitrary generating list.
5. Unique added circuit coordinates do not make the original MRDP witnesses unique.
6. Exact subgroup membership uses integer exponents, including negative ones. A positive-word semigroup would be a different model.
7. Global priority, optimal multiplication-gadget dimension, and a reduced universal-polynomial operation count are not established.
8. No persistent repository or Library mutation was performed.
