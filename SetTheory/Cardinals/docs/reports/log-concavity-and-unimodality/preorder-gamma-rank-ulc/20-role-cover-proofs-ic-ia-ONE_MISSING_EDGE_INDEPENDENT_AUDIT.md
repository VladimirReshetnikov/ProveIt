# Independent audit: one missing balanced core edge

Approved: the three-edge 2+2 core with independent source→exterior→sink attachments has real-stable signed physical monomers, including arbitrary nonnegative independent role activities. Its full gamma polynomial has only negative real roots and satisfies actual-degree ULC. This covers canonical template21, whose core rows are `[0,0,1,3]` and orientation mask12. Relabeling matches the note's missing p2→q2 arc with core vertex2→vertex1.

Final status-only proof pin: `../ONE_MISSING_EDGE_REAL_ROOTEDNESS.md`, SHA256 `650ffac5b1ce132b7cf89b46d28ffc88f4c1fce9874df719d85cdb77513ad8cd`.

## Support identity

The full-core split kernel loses a one-core-edge support exactly when the residual source and sink are forced to be the endpoints of the missing edge. On either side the other center must be unused or matched to an exterior copy private to that center. These are precisely the opposite center's dummy/private parallel class. Common-neighbor copies do not force the residual endpoint and are excluded. Thus the lost signed contribution is restored by +rs. Zero-core-edge supports are unchanged; the two-core-edge support still has the off-diagonal perfect matching and contributes once. The corrected kernel is exactly H=PQ−LM+1+rs, not a matching-count polynomial.

## Arbitrary-class Rayleigh proof

I independently verified all five displayed identities using formal aggregate indeterminates rather than a fixed number of classes. For any remaining class set, write its elementary quadratic as (A²−U)/2, where A is its sum and U its sum of squares. For pair variables x,y, write H=a xy+b x+c y+d; its Rayleigh difference is bc−ad. The separate `check_rayleigh_aggregate.py` reconstructs these coefficients for each of the five cases with A,B,U,V,r,s independent, and verifies exact polynomial equality to the note's SOS expressions.

The five types exhaust distinct class-variable pairs: same side distinguished/ordinary, same side ordinary/ordinary, opposite distinguished/distinguished, opposite distinguished/ordinary, and opposite ordinary/ordinary. Side exchange handles the reflected cases. Empty remainder sets give zero moments and require no exception. Every expression is nonnegative on all real assignments to the original classes: U,V are sums of squares, and products involving U or V distribute into sums of squares. This is an unbounded-class algebraic proof, not an inference from four-class experiments.

H is multiaffine in independent class variables and has constant term1. After proving stability at class level, substitution of nonempty sums of ground variables transfers stability directly. No extra same-parallel-class Rayleigh inequality is needed or assumed.

## Primary source

Petter Brändén, *Polynomials with the half-plane property and matroid theory*, Advances in Mathematics 216(1) (2007), 302–320, Theorem5.6, DOI [10.1016/j.aim.2007.05.011](https://doi.org/10.1016/j.aim.2007.05.011). The [author manuscript](https://arxiv.org/pdf/math/0605678), printed pages9–10, was independently inspected. Its real multiaffine criterion is nonnegativity of every Rayleigh difference at every real assignment. The proof here meets that stronger all-real hypothesis, not merely positive-orthant Rayleigh inequalities.

## Monomers, weights, and finite supplementary check

The subsequent negative-reciprocal substitutions, polynomial denominator clearing, positive split-vertex activity scaling, symbol z+u+v for physical-copy merging, nonzero zero-activity limit, and diagonal gamma-root transfer agree exactly with the independently approved complete balanced proof. Empty-support coefficient1 excludes zero outputs.

The independent Hall checker `../../independent-audit/check_missing_edge_monomer.cpp` separately expands the corrected split kernel and merges physical copies. All 4,845 exterior type multisets through four vertices, including type0 isolates, passed unit, positive-integer, and zero-containing role activities: 14,535 exact multivariate polynomial identities and 251,855 feasible supports checked. These finite tests supplement the arbitrary-exterior ordinary proof.
