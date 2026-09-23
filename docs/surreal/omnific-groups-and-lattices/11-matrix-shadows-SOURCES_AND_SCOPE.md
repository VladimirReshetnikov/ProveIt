# Sources, comparison, and scope

Research date: 23 September 2026.

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/Surreal

Pinned commit: `9693b28c24e6fcb317ce47969a40185c5dfef402`

Inspected through the GitHub connector:
- Repository tree and top-level README.
- `docs/README.md`, containing the catalogue and research/verification status.
- The abstract and introduction of
  `docs/surreal/set-sized-quotients-of-omnific-integers/article.tex`.
- Targeted searches for Steinberg and elementary-matrix terminology.

The quotient article read at that commit is a merged AI-assisted report dated
22–23 September 2026. Its abstract already states constant-term factorization
for set-sized ring images, Gaussian analogues, nonunital targets, set-sized
thresholds, and a countable-versus-finite support distinction. Those are not
claimed as new in this package. The exact support lemma required for the group
arguments is proved directly here.

The GitHub searches did not locate the main elementary-group and Steinberg-group
claims. Searches are not exhaustive and are not a priority certificate. We do
not claim to have fully audited all 51 reports or all source manuscripts in
repository history. The repository was not modified.

## External primary sources

1. Sonia L'Innocente and Vincenzo Mantova, *A factorisation theory for generalised
   power series and omnific integers*, arXiv:1710.07304v5, 22 January 2024.
   https://arxiv.org/html/1710.07304v5
   Role: normal-form and omnific-integer conventions. Its factorization results
   are not used in the new proofs.

2. Egor Voronetsky, *Groups with BC_l-commutator relations*, Journal of Pure and
   Applied Algebra 229(7) (2025), 107966; arXiv:2308.01225v2 (22 February 2024).
   https://arxiv.org/html/2308.01225v2
   DOI: 10.1016/j.jpaa.2025.107966
   Role: existing context for reconstructing coefficient algebra from root
   commutators, including the prior type-A case. The general reconstruction
   idea is not claimed as original here. The finite-tuple small-image lemma is
   proved from scratch and does not import that paper's deeper results.

3. Hyman Bass, John Milnor, and Jean-Pierre Serre, *Solution of the congruence
   subgroup problem for SL_n (n >= 3) and Sp_2n (n >= 2)*, Publications
   Mathematiques de l'IHES 33 (1967), 59–137.
   https://www.numdam.org/item/PMIHES_1967__33__59_0/
   DOI: 10.1007/BF02684586
   Role: the final classical arithmetic step identifying the profinite
   completion of SL_n(Z) with SL_n(Zhat). The real-versus-imaginary warning
   was checked against the paper's printed page 63. The source PDF was
   visually inspected on printed pages 60 and 63.

## Proposed contribution

The proposed original content is the omnific elementary and Steinberg
universal group quotient, the fact that their constant-term kernels themselves
admit no nontrivial set-sized group image, and the structural and cardinal
consequences proved in the manuscript. This is a research proposal with full
proofs, not a certification of historical novelty or a claim to solve a named
longstanding conjecture.

The finite normal-generation and commutator tools are elementary group theory.
The main additional step is to combine their nonunital root-kernel form with
the purely infinite support obstruction, including internally on each conjugate
subgroup of the kernel.

## Claims deliberately excluded

- E_n(Oz) = SL_n(Oz), or the Gaussian counterpart.
- A result in rank two.
- A calculation of K_2 or a universal central extension theorem in every rank.
- Triviality of all class-sized representations.
- Exact image thresholds for every explicit fragment without extra assumptions.
- A claim that every finite subgroup is conjugate to a constant one.
- Formal Lean verification, independent refereeing, or exhaustive literature review.
