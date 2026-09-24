# Literature and claim status

Status check: 20 September 2026. These statements concern the source versions
listed below. They are not a guarantee that every unpublished or unindexed
argument has been found.

## Target and prior results

1. Christos A. Athanasiadis and Frédéric Chapoton, *Polytopes and posets
   associated to preorders*, arXiv:2605.26916v1, 26 May 2026.
   https://arxiv.org/abs/2605.26916v1
   Section 5 defines the support polynomial and states Conjecture 5.1(c):
   it is the h-polynomial of an n-dimensional simplicial polytope. Parts (a)
   and (b) ask for palindromicity and unimodality. Part (d) asks for a flag
   realization. Conjectures 5.2 and 5.3 ask for gamma-positivity and
   real-rootedness; Conjecture 5.4 asks for invariance under order reversal.

2. Ziyi Dai, Qilin Hou, Zhiyuan Liu, Warut Thawinrak, and Hongyu Wang,
   *Counting Lattice Points in Minkowski Sums of Cross Polytopes*,
   arXiv:2608.16037v2, 27 August 2026.
   https://arxiv.org/abs/2608.16037v2
   Theorem 1.2 already identifies graph support-enumerators with the Ehrhart
   numerators of augmented bipartite root polytopes. Theorem 1.3 already
   proves duality and explicitly settles Athanasiadis–Chapoton Conjecture 5.4.
   Problem 5.3 still discusses the preorder coefficient-shape conjectures.
   The higher-dimensional identity and duality are NOT novelty claims here.

3. Krishna Menon, *Gamma-positivity for octopuses: a bijective proof*,
   arXiv:2608.13247v1, 13 August 2026.
   https://arxiv.org/abs/2608.13247v1
   Provides special-case gamma-positivity results, not the general
   simplicial-polytopal realization proved in the present manuscript.

## Proposed additions in this manuscript

- The explicit n-dimensional directed root polytope C_tau, with vertices
  +/-e_i and e_i-e_j for j <=_tau i and i != j.
- A complete weighted-Hall description of the larger polytope B_tau.
- A unique integer-fiber parametrization of B_tau over C_tau, implying
  Ehr_B(t) = Ehr_C(t)/(1-t)^n and h*(C_tau,t) = h_tau(t).
- Reflexivity of C_tau, an exact maximum-weight-ideal gauge, and unimodular
  cones over every vertex-only boundary triangulation.
- Simplicial-polytopal realization of h_tau by a pulling boundary; hence
  the conclusions in Conjecture 5.1(a,b,c) and the full g-theorem conditions.
- A second route using a diagonal special simplex, and an explicit interior
  lattice-point translation for B_tau.

## Established theorems used

Athanasiadis, arXiv:math/0312031, Lemma 2.1 supplies polytopality of a pulling
boundary; Theorem 3.5 supplies the independent special-simplex route.
The support-enumerator identity is imported from Dai et al., Theorem 1.2.
An appendix instead reconstructs that identity from the Kálmán–Postnikov
interior-polynomial theorem (arXiv:1602.04449, Theorem 1.1 and equation 1.2).
Dehn–Sommerville and the g-theorem give the coefficient consequences.

## Not claimed

- A new proof of a still-open duality conjecture: duality was already settled.
- A proof of flag realizability, gamma-positivity, or real-rootedness.
- A proof about arbitrary reflexive nontransitive relations.
- That the support polynomial is h*(Q_tau); it is h*(B_tau) and h*(C_tau).
- Peer review, proof-assistant verification, or guaranteed absolute priority.

The article contains a proposed complete mathematical argument, rather than
an unproved reduction of the target to a new conjecture. Independent review
should focus on the exact Hall reduction, the inverse fiber parameters, and
the application of the polytopal pulling lemma. Computational agreement is
supporting evidence only.
