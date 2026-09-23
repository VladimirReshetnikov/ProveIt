# Source and claim audit

## Baseline

Repository: VladimirReshetnikov/Surreal
Commit: 71e9606d297c9b98c732070dc462682cc6948981
Inspection date: 23 September 2026

Inspected materials included the root README, docs/README.md, and the README
and relevant source passages of
`docs/surcomplex/entire-functions-at-arbitrary-rank/`.
A repository search for “rectification” returned no match. That negative
search is not proof of absence under other terminology, nor a complete audit
of every source in the repository.

The existing report already contains the all-scale coefficient criterion,
canonical products and division, order-unit interpolation, a sharper infinite
jet image theorem, and several-variable scalar-extension results. These are
explicitly credited; independent proofs of the subset used here are included.

## Primary literature consulted

- Rosay–Rudin, Holomorphic maps from C^n to C^n, Trans. AMS 310 (1988), 47–86.
  https://www.jstor.org/stable/2001110
- Winkelmann, Rosay-Rudin-Spaces, Tame Sets and Danielewski Surfaces,
  arXiv:2309.07678v1. Its introductory definitions distinguish classical
  tameness from the line-rectifiability property used in this manuscript.
  https://arxiv.org/html/2309.07678v1
- Cherry, Lectures on Non-Archimedean Function Theory, arXiv:0909.4509.
  https://arxiv.org/abs/0909.4509
- Mantova–Matusinski, Surreal numbers with derivation, Hardy fields and
  transseries: a survey, arXiv:1608.03413v2.
  https://arxiv.org/html/1608.03413v2
- L’Innocente–Mantova, A factorisation theory for generalised power series
  and omnific integers, arXiv:1710.07304v5; DOI 10.1016/j.aim.2024.109513.
  Used for the normal-form description of omnific integers, not as evidence
  for the newly proposed geometric theorems.
  https://arxiv.org/html/1710.07304v5

Focused searches included “Hahn entire automorphisms”, “Hahn tame discrete
sets”, and “Hahn fat point”. No matching statement of the precise new
classification was located. This bounded search does not certify novelty.

## Proposed contributions

- The exact order-unit dichotomy for line-rectification of every radially
  finite configuration in dimension at least two.
- Eventual polynomial reductions of an entire automorphism and its inverse
  along a proper convex-subgroup exhaustion.
- An explicit escaping infinitesimal-simplex obstruction to every entire
  coordinate automorphism, even with an arbitrary affine hyperplane target.
- Polynomial-part, real omnific, and Gaussian omnific rectification without
  assuming an order unit.
- An explicit global fat-point ideal formula and the sharp minimal generator
  count in arbitrary rank, plus the unbounded-multiplicity consequence.

The projection-and-shear method is classical. The local homogeneous-jet
counting method is elementary algebra. Neither method by itself is claimed
as a novel invention. The novelty assessment concerns their precise Hahn-
workspace consequences and the coarsening obstruction.

## Non-claims

- No named published conjecture is said to be solved.
- No classification of all entire ideals or all entire automorphisms.
- No assertion that arbitrary bijections of omnific configurations extend.
- No assertion that a rectifying map preserves the omnific ring.
- No unrestricted product description of the infinite evaluation quotient
  without an order unit.
- No use of countably infinite analytic sums as algebraic ideal generation.
- No class-global entire theory on all of No or No(i).
- No Lean verification or independent peer review.

The mathematical proof audit is in Sections 10–11 of the article. The
finite symbolic program is deliberately described as a sanity check only.
