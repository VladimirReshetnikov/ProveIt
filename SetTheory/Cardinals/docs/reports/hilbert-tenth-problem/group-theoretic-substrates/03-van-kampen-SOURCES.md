# Sources and claim boundary

Consulted October 2, 2026. This is a targeted dependency review, not an
exhaustive priority search or a certification of the entire ProveIt repository.

## Repository snapshot

`VladimirReshetnikov/ProveIt` at
`c58206ca101d4744a015a0f0104646109357d943`.

Relevant inspected documents:

1. `Computability/HilbertTenthProblem/Lean/MRDP.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/c58206ca101d4744a015a0f0104646109357d943/Computability/HilbertTenthProblem/Lean/MRDP.md
   Identifies the natural-input, natural-witness, fixed-finite-polynomial
   endpoint and distinguishes its existence statement from numerical compiler
   bounds. Its documented builds were not rerun here.

2. `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/group_projective_label_aligned_lanes.md`
   https://github.com/VladimirReshetnikov/ProveIt/blob/c58206ca101d4744a015a0f0104646109357d943/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/group_projective_label_aligned_lanes.md
   Existing packed controller-lane optimization. This report does not improve
   or inherit that construction's arithmetic-operation counts.

## Mathematical sources

- I. N. Sanov, *A property of a representation of a free group*, Doklady
  Akademii Nauk SSSR (N.S.) 57 (1947), 657–659. Historical original.
- A. Chorna, K. Geller, V. Shpilrain, *On two-generator subgroups in SL_2(Z),
  SL_2(Q), and SL_2(R)*, arXiv:1605.05226v4.
  https://arxiv.org/abs/1605.05226
  The PDF's first page was visually inspected: Theorems 1–2 give precisely
  the free shear group and its congruence/determinant description. The report
  includes direct proofs rather than treating this chart as new.
- Y. Cornulier, R. Tessera, *Geometric presentations of Lie groups and their
  Dehn functions*, arXiv:1310.5373v2.
  https://arxiv.org/abs/1310.5373
  Lemma 2.D.2 on printed page 28 was visually inspected. It gives conjugator
  lengths at most n+L*area. It is an imported lemma used for the height theorem.
- W. W. Boone, *The word problem*, Annals of Mathematics (2) 70 (1959),
  207–265. https://www.jstor.org/stable/1970103
  Historical source for undecidable finitely presented group word problems;
  no explicit relator table from this article is instantiated in the code.
- G. Higman, B. H. Neumann, H. Neumann, *Embedding theorems for groups*,
  Journal of the London Mathematical Society 24 (1949), 247–254.
  Historical source for the effective two-generator embedding construction.
- M. R. Bridson, C.-F. Nyberg-Brodda, *HNN extensions and embedding theorems
  for groups*, arXiv:2512.10800.
  https://arxiv.org/abs/2512.10800
  The consulted public text details the two-generator embedding and explicit
  word substitution in Section 2.3, and the word-problem context in Section 3.1.

## Research contribution and limits

The report's proposed contribution is its explicit area and DAG quartic
compiler synthesis, literal witness/residual ledgers, semantic zero-tuple
bijections, sharp dyadic product-gate theorem, and addition-chain refinement.
The proof of exact rectangular area and the Dehn/decidability connection are
presented as elementary or classical ingredients, not new group theory.

No exhaustive search establishes priority for this synthesis. No claim is
made to resolve unrestricted finite-fold MRDP, produce a universal numerical
presentation, improve a universal arithmetic-operation record, or certify
any new result in Lean/Rocq. The repository itself remains unchanged.
