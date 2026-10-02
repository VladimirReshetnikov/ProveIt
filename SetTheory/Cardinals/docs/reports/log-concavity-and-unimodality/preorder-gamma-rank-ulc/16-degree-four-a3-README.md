# Complete rank-four three-attachment sector

**Status: proved, with separate independent kernel/coverage and positivity audits.**
The producer's standalone exact verifier also passes. All certificates use integer
or rational identities; numerical optimization was only a discovery tool.

## Complete family

The established Gallai–Edmonds a=3 reduction gives a preorder core K with at most
six vertices and three distinguished attachments A. Exterior vertices are mutually
independent and adjacent only to A; each attachment has one common strict exterior
orientation. There are at most seven nonempty neighborhood types. Padding K with
isolated vertices gives a six-element core without changing gamma. Since K−A has
only three vertices, its matching number is automatically at most one. Every full
graph has matching number at most four.

The enumeration tries every six-element preorder through exact quotient posets
and positive block compositions, every marked triple, and all eight orientation
masks. A type is checked with two identical independent copies, and the complete
union of legal types is checked for transitivity. Every type may have population zero.

Structural pruning uses one copy of each legal type to identify components and
bipartiteness. At three copies per legal type, the exact matching rank of a component
is the number of its active attachments plus the matching rank of its remaining
core vertices. The upper bound follows by removing edges incident with active
attachments; it is attained by matching each active attachment to a distinct
exterior clone, then using a maximum matching in the remaining core. Thus a
component with maximum rank at most three is covered by the established theorem;
a bipartite component is covered by the established bipartite result. Product
closure covers their disjoint union. Only nonbipartite rank-four components remain.

Results:

- 854 weighted core cases
- 90,042 legal marked/oriented specifications
- 68,704 specifications settled structurally
- 21,338 retained specifications
- 6,213 canonical templates, modulo attachment/rest permutations and duality
- 3,437 coefficient-distinct gamma polynomials

The support kernel directly enumerates ordered disjoint endpoint subsets. Every
selected exterior vertex is mandatory, and feasibility is tested by a directed
perfect matching. At most three exterior vertices occur, giving the exact
multivariate binomial expansion for quotas of total size at most three.

## Exact positivity

The second Newton gap is quartic, and the third has degree at most six. The known
universal first inequality needs no new certificate. Set G=6*gamma to clear every
binomial denominator. The exact targets are

`4 G2²−9 G1 G3` and `3 G3²−8 G2 G4`.

Each is 36 times its original integer Newton gap. Nonnegative binomial coefficients
certify a target on all nonnegative integer populations. Otherwise split each
coordinate into x_i=0 or x_i=1+y_i with y_i≥0. Nonnegative ordinary coefficients
or exact orthant square certificates cover every face.

There are 63,917 nontrivial face aliases and 53,722 distinct normalized target
polynomials. The final ledger uses 53,477 binomial-square certificates and 245
general-square certificates, together with positive monomials. Independent replay
checked 315,706 binomial squares, 4,467 general squares, and 3,701,522 positive
monomials. All weights are strictly positive.

## Authoritative replay files

- `a3_polynomials.jsonl`: all 6,213 templates and direct support coefficients
- `a3_unique_gamma.jsonl`, `a3_gamma_aliases.json`: coefficient-identical reduction
- `coefficient_certificates.json`: directly positive binomial/ordinary cases
- `normalized_faces.jsonl`: sparse exact target polynomials and variable counts
- `face_aliases.json`: positive scaling and variable maps for every nontrivial face
- `certificates.jsonl`: one selected exact certificate per normalized target
- `verify_certificates.py`, `verification.json`, `verify_certificates.log`: complete
  standard-library exact replay, with no producer or numerical-library imports

A normalized face may omit unused coordinates. Its permutation indexes the active
face coordinates; every omitted coordinate has exponent zero in the entire face.
The permuted face equals its positive integer scale times the normalized target.

A certificate of kind `binomial` represents a square as
`weight * x^m * (u*x^a − v*x^b)^2`.
A certificate of kind `general` represents it as
`weight * x^m * (sum c_e*x^e)^2`.
Both formats separately list positive monomials. All coefficients and weights are
rational strings and are checked exactly.

## Independent audits

The separate audit in the sibling directory
`preorder-gamma-degree4-independent-audit/three-attachment/` regenerated coverage
without the producer's quotient/canonicalization code, independently counted all
188,715 quota vectors and 943,575 coefficients by Hall's theorem, and checked all
6,213 representatives and gamma aliases. Its positivity audit separately rebuilt
both gaps, all 204,388 integer faces, every face normalization, and every rational
square identity without importing the producer or its verifier.

The a=3 sector is therefore settled. The only remaining rank-four branch in the
established GE reduction is a=4, investigated separately under `four-attachment/`.
