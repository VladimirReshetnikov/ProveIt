# Sources and scope

## Repository snapshot

Repository: https://github.com/VladimirReshetnikov/ProveIt

The recursively fetched `main` tree on 30 September 2026 had revision:

`6996fee43cc97b6c16351def7507d59a95bf62f0`

Relevant inspected material:

1. `Algebra/SurrealNumbers/README.md`: normal-form support of the omnific ring,
   real-vector-space purely infinite part, constant extraction, finite-element
   rigidity, unique omnific floor, and ordinary congruences. The relevant
   foundation passage was also re-fetched at the pinned revision.
2. `Logic/PresburgerArithmetic/README.md`: ordinary integer Cooper elimination
   in Lean and the independent normalized one-variable Rocq/Coq proof. Also
   re-fetched at the pinned revision.
3. `Algebra/SurrealNumbers/docs/README.md`: report catalog and review boundaries.
4. `Algebra/SurrealNumbers/docs/surreal/omnific-groups-and-lattices/README.md`:
   related rational-flag and missing-lattice-minimum work. The scope comparison
   is based on this README, not on a full independent review of its merged
   95-page report.

The manuscript bibliography uses pinned repository URLs. No repository files
were modified and no Lean/Rocq project build was performed.

## Primary mathematical sources

- Emil Jeřábek, *Rigid models of Presburger arithmetic*, arXiv:1803.05797v2;
  Mathematical Logic Quarterly 65 (2019), 108–115. Used for the classical
  Z-group completeness and quantifier-elimination framework.
- Raf Cluckers, *Presburger sets and p-minimal fields*, arXiv:math/0206197;
  Journal of Symbolic Logic 68 (2003), 153–162. Related context for finite
  linear/congruence parameter descriptions.
- Shmuel Onn, *Nonlinear Discrete Optimization: An Algorithmic Theory*, EMS,
  2010, DOI 10.4171/093. Classical Graver and integer-optimization framework.
- Shmuel Onn and Michal Rozenblit, *Convex Integer Optimization by Constantly
  Many Linear Counterparts*, arXiv:1208.5639v1. Classical zonotope refinement,
  chamber counting, and Graver edge-direction antecedents. The bibliography
  identifies the consulted arXiv version explicitly.

The bibliography metadata and primary online sources were checked during
preparation. Relevant pages in the research PDFs were visually inspected.

## Contribution and novelty boundary

The draft develops the explicit bounded-slack candidate formula, the
set-sized Presburger localization needed for a full-class surreal reading,
the finite tail/residue face-lattice compiler, same-matrix descent, and the
universal rational-normal dichotomy. It adds an integer-right-hand-side
irrational example whose failure is exposed by an infinitesimal objective.

The general phenomenon of irrationality obstructing omnific lattice extrema
already has related treatments in the repository, and the finite Graver and
zonotope machinery is classical. The manuscript does not claim either of
those ingredients as newly discovered. A targeted source comparison does
not establish publication priority for the resulting theorem package.

The questions settled are explicitly formulated in this manuscript. There
is no claim to have solved a named long-standing conjecture. Independent
mathematical review remains appropriate before treating this as an established
research contribution.

## Computational boundary

`verify.py` checks finite specializations of the 2–3 knapsack family, the
explicit conformal decomposition in that example, finite local/global
augmentation equivalence, and four exact rational-square witnesses.
It neither represents arbitrary surreal numbers nor establishes the general
proofs by finite experimentation. The infinitesimal-objective example is
proved mathematically, not tested by a numerical surrogate.
