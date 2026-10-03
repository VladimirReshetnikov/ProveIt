# Same-sign two-attachment role-weighted reduction

Status: independently audited and approved. All 257 shared-cone rational identities and all 333 private-only reductions are complete. The external audit regenerated all 590 same-sign core templates, checked all 257 symbolic moment formulas and 1,028 heterogeneous/zero-face cases, and verified 7,866 square terms plus 32,729 positive remainder terms. This proves the entire role-weighted same-sign a=2 branch for arbitrary populations.

## Scope

Retain the GE core K, with at most five vertices and marked attachments i=0,j=1. Exterior vertices are independent and have neighbors only in {i,j}. Suppose the directions at both attachments agree. By order duality, exchange tail/head activities and assume every exterior vertex is a head. The legal types are {i}, {j}, and {i,j}; any may be absent. We seek the cubic inequality gamma_2^2 >= 3 gamma_1 gamma_3 for arbitrary positive core activities and heterogeneous exterior head activities. The first Newton inequality and all original degree-at-most-two cases are already universal.

## Exact finite moment reduction

For the private clouds put A=sum v_x over type {i} and B=sum v_x over type {j}. For the shared cloud put

U=sum v_x,   E=sum_(x<y) v_x v_y.

Let F_i=z u_i Gamma_(K-i), F_j=z u_j Gamma_(K-j), and G=z^2 u_i u_j Gamma_(K-{i,j}). Define F_* as the contribution of all supports using a single newly adjoined head of type {i,j}, with that head's activity set to one. This is a support kernel: if either attachment can match the common head, the same final support is counted only once. In general F_* is not F_i+F_j.

The exact identity is

Gamma = Gamma_K + A F_i + B F_j + U F_*
        + [AB+(A+B)U+E] G.

There are at most two exterior vertices in a support. A single exterior vertex gives its displayed kernel. If two are selected, they must be matched to the two attachments. Each allowed pair of private/shared types has a unique endpoint support, whatever the number of witnessing matchings. Removing both attachments and both exterior heads leaves precisely a support of K-{i,j}. Two heads from the same private cloud are impossible. Summing the remaining type patterns gives AB, AU, BU and E. This proves the identity for arbitrary cloud sizes and heterogeneous weights.

The only information needed about the shared cloud is

U>=0,   0<=E<=U^2/2,

because 2E=U^2-sum v_x^2. Parameterize this entire closed cone by

U=xi+eta,   E=2 xi eta,   xi,eta>=0.

Indeed, for any point in the cone the two nonnegative parameters are (U+sqrt(U^2-2E))/2 and (U-sqrt(U^2-2E))/2. This is an algebraic positivity reduction; it does not claim that every point is realized by a fixed finite number of positive heads. Proving the cubic gap on the whole closed cone is sufficient.

For exact support-polynomial generation, adjoin the legal private heads with activities A,B and two common heads with activities xi,eta. Count a support containing both common heads with coefficient two rather than one. All other supports have their ordinary coefficient one. Since a support contains at most two exterior heads, the resulting formal polynomial is exactly the above substitution E=2xi eta. It is not being identified with an ordinary two-common-head preorder polynomial.

## The private-only branch

If both singleton head types are legal, their union is also legal. A new head has no outgoing arcs, and its incoming set is transitive precisely when it contains all core predecessors of its members. The union of two such predecessor-closed sets is predecessor-closed. Therefore, if the common type is not legal, at most one singleton type is legal. Sum that one cloud into a single head. The result has at most six vertices and the independently audited six-vertex role-weighted theorem applies.

The catalog has 333 such same-sign private-only templates and 257 same-sign templates permitting a shared cloud. Together they are the 590 same-sign members of the independently audited 1,084-template catalog. The remaining 494 opposite-sign templates are covered by the separately approved mixed-sign compression theorem in `A2_MIXED_ROLE_ULC.md`.

## Rational identities and independent local checks

The shared-cone certificate files are `a2_same_sign_certificates/t%04d.json`, indexed by the original catalog ID. Each supplies an exact representation of the substituted cubic gap as a sum of nonnegative monomial multiples of rational polynomial squares plus a polynomial with nonnegative coefficients. It is valid throughout the nonnegative orthant in core activities and A,B,xi,eta.

Run `python verify_a2_same_sign_cone.py`. This standard-library checker imports no producer or original support kernel. It independently uses Hall's criterion to reconstruct all supports, derives F_* using a single common head, checks the full forced-pair formula symbolically for all 257 templates, checks rational examples with three heterogeneous common heads, and verifies every saved square identity exactly. It also checks all 333 private-only reductions. The completed receipt `a2_same_sign_cone_verification.json` has `all_shared_templates_certified: true` and no missing certificates. The final source225 certificate uses the original direct identity, without a multiplier or chamber split.

The source catalog completeness and the GE core bound are explicit inputs from `../preorder-gamma-degree3/two-attachment/INDEPENDENT_AUDIT.md` and `../preorder-gamma-degree3/THEOREM_SYNTHESIS.md`. Original activities are positive, so the original actual degree is known. The artificial moment parameterization and possible zero effective weights never justify replacing actual-degree-two normalization by a padded degree-three claim.
