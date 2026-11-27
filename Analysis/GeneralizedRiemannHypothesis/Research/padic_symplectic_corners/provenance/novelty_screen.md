# Novelty screen: symplectic compressions over complete discrete valuation rings

Search date: 2026-11-26 (Pacific user date).

## Candidate statements screened

1. For primitive frames V and X and Haar S in Sp(2g,O), the derivative of S -> V^t J S X has cokernel dimension d(d-1)/2, where d is the intersection dimension of the two reduced frame subspaces.
2. On every residue class with d<=1, higher digits of the compression are exactly uniform. Globally the discrepancy from the uniform-digit lift of its finite-field law is bounded by the probability d>=2, and an explicit two-plane overlap moment gives O(q^(-4g)) at fixed frame dimensions.
3. For symplectic two-frames, the exact density is a geometric sum in v(1-det A), and total variation from iid additive Haar is independent of precision, equal to (1-q^(-1)+q^(-3))(q^2-1)/(q^(2g)-1).

This is a targeted literature screen, not a proof of absolute priority. No matching theorem or stronger exact symplectic-compression law was located among the primary sources below. The general use of Lie-algebra lifting and a bad-residue-class bound is explicitly prior work.

## Closest primary sources

### P1. Noam Pirani (2024), Traces of powers of random matrices over local fields

- https://arxiv.org/abs/2408.04061
- https://arxiv.org/html/2408.04061v1
- Inspected: Introduction, Section 2.4, Sections 8.2.1-8.2.3, especially Lemma 8.5 and Propositions 8.6 and 8.8.
- Content: congruence-layer Lie-algebra lifting for compact classical groups, including symplectic groups; exact uniform higher digits for characteristic-polynomial coefficients on a good residue set; total-variation error controlled by exceptional mod-uniformizer classes, uniformly in precision. Assumes odd residue characteristic.
- Difference: its maps are traces and characteristic coefficients; its good condition is a lower bound on minimal-polynomial degree. It does not state a rectangular compression law, the intersection-defect identity, the two-plane overlap error, or the proposed exact 2-by-2 density.
- Required attribution: the lifting strategy, higher-digit uniformity principle, and exceptional-set comparison must not be claimed as new.

### P2. Roger Van Peski (2021), Limits and fluctuations of p-adic random matrix products

- https://arxiv.org/abs/2011.09356
- https://arxiv.org/pdf/2011.09356
- Selecta Mathematica 27, article 98 (2021); DOI https://doi.org/10.1007/s00029-021-00709-3
- Inspected: Theorem 1.3, Corollary 1.4, proof of Theorem 1.3 in Section 3, discussion of general local fields and Appendix A.
- Content: exact Hall-Littlewood laws for singular numbers of rectangular corners of Haar GL_N(Z_p) matrices and their products; extension to general non-Archimedean local fields.
- Difference: multiplicative group is GL, not Sp. The appendix's symplectic statements concern the Archimedean/quaternionic comparison. This does not supply the candidate symplectic compression density.

### P3. Jiahe Shen and Roger Van Peski (2024/2025), Non-Archimedean GUE corners and Hecke modules

- https://arxiv.org/abs/2412.05999
- https://arxiv.org/html/2412.05999v2
- Inspected: abstract, version history and introduction synopsis. HTML omits most body sections, so no full proof inspection is claimed.
- Content: joint singular-number laws for principal corners of additive-Haar alternating or Hermitian matrices, with Hall-Littlewood structure.
- Difference: an additive-Haar alternating matrix is not a Haar-distributed element of Sp. The observed random object and constraints differ from the proposed compression theorem.
- Scope detail: v2 explicitly corrects the earlier claim of validity in positive characteristic; the published argument is for p-adic fields. The candidate theorem's complete-DVR scope should be established directly, without relying on that paper.

### P4. Yury Neretin (2013), Hua measures on the space of p-adic matrices and inverse limits of Grassmannians

- https://arxiv.org/abs/1205.2113
- https://arxiv.org/html/1205.2113v1
- Izvestiya: Mathematics 77(5), 941-953 (2013); DOI https://doi.org/10.1070/IM2013v077n05ABEH002665
- Inspected: Theorems 1.1-1.3 and Section 1.7.
- Content: Hua measures on Q_p matrix spaces, consistent corner projections, Grassmannian interpretations, and symmetric/alternating variants including the Lagrangian Grassmannian.
- Difference: these are matrix-space or Grassmannian chart measures under fractional-linear actions. They do not state the law of the raw 2-by-2 block of Haar Sp(2g,O), nor the proposed total-variation identity.

### P5. Derek Garton (2015), Random matrices, the Cohen-Lenstra heuristics, and roots of unity

- https://arxiv.org/abs/1405.6083
- https://msp.org/ant/2015/9-1/ant-v9-n1-p05-s.pdf
- Algebra & Number Theory 9(1), 149-171; DOI https://doi.org/10.2140/ant.2015.9.149
- Inspected: main setup and Sections 2.1-2.2; relevant orbit-moment formulas.
- Content: cokernels of I-S for Haar symplectic similitudes over Z_l, with arithmetic-statistics applications and finite-ring reductions.
- Difference: observable is a full-size cokernel, not a fixed rectangular compression. Its Haar-reduction facts are useful background, but no matching block law appears.

### P6. Hoi H. Nguyen and Melanie Matchett Wood, Local and global universality of random matrix cokernels

- https://arxiv.org/abs/2210.08526
- Inspected: abstract/metadata.
- Content: universality of cokernels for integral symmetric, skew-symmetric and Laplacian models.
- Difference: these are structured additive matrix models. This is related background, not evidence of a multiplicative-Haar symplectic compression theorem.

### P7. Jason Fulman and Nathan Kaplan, Random Partitions and Cohen-Lenstra Heuristics

- https://arxiv.org/abs/1803.03722
- https://dornsife.usc.edu/jason-fulman/wp-content/uploads/sites/224/2023/06/cokernelsfinal.pdf
- Inspected: abstract and the model identification through the authors' paper and Shen-Van Peski's discussion.
- Content: partition distributions related to Cohen-Lenstra measures and cokernels of structured additive p-adic matrices.
- Difference: not the symplectic-group block ensemble. Do not confuse “symplectic” used for alternating forms in finite-field rank literature with the group Sp.

## Novelty framing recommended

The robust statement is: “We derive the following symplectic-compression theorems. The finite-field frame-counting input belongs to the earlier report; the congruence-lifting principle has precedents such as Pirani. The new contribution developed here is the exact intersection defect, the explicit precision-uniform comparison, and the 2-by-2 density and precision-independent total variation. A targeted search of the primary sources above found no matching statement.”

Avoid asserting that a worldwide priority search is complete. Do not claim the elementary dot-product local density used in the 2-by-2 computation as a new general technique. Its role is a direct counting lemma. The exact total-variation identity and its interpretation are stronger and more distinctive than the existence of a geometric-sum density alone.

## Interpretive boundary

Exact preservation of total variation under reduction mod pi means that an optimal equal-prior binary test can use only the residue matrix. It does not mean higher digits are independent of the source ensemble or that the full likelihood ratio is determined by the residue matrix. The density explicitly varies with v(1-det A), so the latter assertions would be false.

## Search coverage

Queries used both available engines and included:
- p-adic symplectic Haar random matrix corners/truncations;
- symplectic Haar blocks/submatrices over Z_p and finite local rings;
- symplectic p-adic total variation;
- p-adic matrix beta, Jacobi, Hua measures;
- local representation densities for alternating forms;
- top-left/2-by-2 symplectic block distributions;
- Van Peski, Neretin, Fulman, Kaplan, Wood and symplectic cokernels.

The important positive discovery was P1; the absence of direct matches in other searches is only limited novelty evidence.
