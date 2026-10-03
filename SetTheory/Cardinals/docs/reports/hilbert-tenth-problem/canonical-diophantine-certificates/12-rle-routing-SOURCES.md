# Provenance and literature boundary

Consulted on September 30, 2026. The bibliography in `article.tex` is the primary
citation list. The links below identify the inspected materials, not an exhaustive
literature search or an independent audit of all repository claims.

## Pinned ProveIt sources

Snapshot: `e18718e837d43e162252f9a314e8cb797fbd1a1f`.

- Project: https://github.com/VladimirReshetnikov/ProveIt
- Hilbert's tenth problem README:
  https://github.com/VladimirReshetnikov/ProveIt/blob/e18718e837d43e162252f9a314e8cb797fbd1a1f/Computability/HilbertTenthProblem/README.md
- MRDP specification and proof-chain guide:
  https://github.com/VladimirReshetnikov/ProveIt/blob/e18718e837d43e162252f9a314e8cb797fbd1a1f/Computability/HilbertTenthProblem/Lean/MRDP.md

These identify the existing `Diophantine.mrdp` natural-witness interface. Its
existence assertion does not supply the new canonical routing compilers or
establish single-foldness. This package does not rebuild the repository.

## Primary literature

1. Tobias Friedrich and Lionel Levine, *Fast simulation of large-scale growth
   models*, arXiv:1006.1003v2. Theorem 1 and its least-action/acyclicity mechanism.
   https://arxiv.org/abs/1006.1003
2. Benjamin Bond and Lionel Levine, *Abelian networks I. Foundations and examples*,
   SIAM J. Discrete Math. 30(2), 856–874 (2016), arXiv:1309.3445.
   https://arxiv.org/abs/1309.3445
3. Bernd Gärtner et al., *ARRIVAL: Next Stop in CLS*, ICALP 2018,
   arXiv:1802.07702. Unique run-profile witnesses and UP intersect coUP.
   https://arxiv.org/abs/1802.07702
4. John Fearnley, Martin Gairing, Matthias Mnich, and Rahul Savani,
   *Reachability switching games*, LMCS 17(2), article 10 (2021),
   arXiv:1709.08991v7. Binary run-length succinctness in Section 2 and
   last-used-edge structure in Section 5.3.
   https://arxiv.org/abs/1709.08991
5. Hannah Cairns, *Some halting problems for abelian sandpiles are undecidable
   in dimension three*, arXiv:1508.00161v2. Context for universal abelian
   computation on suitable infinite backgrounds, not a universality theorem
   for the finite periodic rotor model.
   https://arxiv.org/abs/1508.00161
6. Jonas Bayer et al., *Diophantine equations over Z: universal bounds and
   parallel formalization*, arXiv:2506.20909v1. Context for explicit complexity
   accounting and the formalization boundary.
   https://arxiv.org/abs/2506.20909

## Novelty and verification

The last-exit method, ordinary MRDP, run-length switching orders, and standard
ARRIVAL uniqueness results are prior work, not new discoveries claimed here.
The exact compilers and representation-boundary theorems are developed with
proofs in this article. Their literature priority has not been verified. The
single-fold and finite-fold representation principles remain hypotheses in the
conditional theorem, not conclusions asserted without proof. The source search
does not establish the current worldwide status of every research question.

The new material is not Lean-checked. The Python programs provide exact finite
checks and an explicit coefficient-level RLE compiler. They do not establish
infinite semantic theorems by testing, and they do not encode and verify a full
universal Turing machine.
