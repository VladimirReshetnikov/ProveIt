# Full core-variable Rayleigh differences from the boundary theorem

Status: ordinary corollary of the independently audited computer-assisted boundary theorem; supplementary exact middle-coefficient check also passes. October 1, 2026. The released six-page bipartite-and-pendant package is unchanged.

Use the definitions in `COEFFICIENTWISE_BOUNDARY_LEMMA.md`. Thus

    F(z_0,z_1,z_2)
      = z_0 z_1 z_2 + sum_i a_i z_j z_k + sum_(i<j) b_ij z_k + c,

where the coefficients include independent formal tail/head activity variables and count each feasible ordered physical support once. There are no internal physical core arcs.

## Claim

For every distinct i,j,k in {0,1,2}, the Rayleigh difference

    Delta_(z_j,z_k)(F) = (partial_(z_j)F)(partial_(z_k)F)
                         - F partial_(z_j)partial_(z_k)F

is coefficientwise nonnegative in all core monomer and original role-activity variables. In particular F, as a polynomial of its three core monomers, is Rayleigh under every nonnegative independent role activity specialization.

This is positivity for nonnegative monomer arguments. It is not the all-real Rayleigh criterion for real stability, and no real-stability conclusion is inferred.

## Algebraic expansion

Directly expanding and canceling z_j,z_k gives

    Delta_(z_j,z_k)(F)
      = (a_j a_k - b_jk) z_i^2
        + (a_j b_ik + a_k b_ij - c - a_i b_jk) z_i
        + (b_ij b_ik - a_i c).

The constant coefficient is coefficientwise nonnegative by the audited boundary theorem. The quadratic coefficient is elementary: every size-two support using core j,k has at least one pair of witnessing single-edge supports counted by a_j a_k, with the same role weight. Repeated exterior vertices and extra matching witnesses add only nonnegative contributions to that product.

## A fresh private head proves the middle coefficient

Adjoin a new exterior physical vertex x and only the arc i→x. Set L=u_i v_x. The new vertex has no other arcs, so any support using it must use that one edge. For the enlarged relation the coefficients are exactly

    a_i' = a_i + L,
    b_ij' = b_ij + L a_j,
    b_ik' = b_ik + L a_k,
    c' = c + L b_jk.

Deleting the forced edge gives a bijection of endpoint supports; any residual matching-witness multiplicity remains ignored. The coefficients a_j,a_k,b_jk are unchanged.

The enlarged graph still has the same three-vertex physical core and an independent exterior, so the boundary theorem applies to it. Its boundary gap expands to

    b_ij' b_ik' - a_i' c'
      = (b_ij b_ik - a_i c)
        + L (a_j b_ik + a_k b_ij - c - a_i b_jk)
        + L^2 (a_j a_k - b_jk).

The fresh variable v_x does not occur in any original coefficient. Extracting its coefficient from this coefficientwise nonnegative polynomial shows that

    u_i (a_j b_ik + a_k b_ij - c - a_i b_jk)

is coefficientwise nonnegative. Multiplication by the monomial u_i merely shifts exponents injectively, so the parenthesized polynomial is itself coefficientwise nonnegative. This proves the middle coefficient and completes the claim.

Equivalently, inserting private exterior heads at the core vertices translates the core monomer variables by their edge activities. The boundary inequality for the enlarged graph therefore controls the complete core-variable Rayleigh difference.

## Negative-correlation interpretation

Fix nonnegative role activities and strictly positive core monomer activities z_i. Give each feasible ordered support probability proportional to its role weight times the product of z_i over its unused core vertices. The normalizing constant F(z) is positive because the empty support contributes z_0 z_1 z_2.

For distinct core vertices j,k, the covariance of their unused indicators is

    Cov(1_(j unused),1_(k unused))
      = z_j z_k [F F_(z_j z_k)-F_(z_j) F_(z_k)] / F^2
      = -z_j z_k Delta_(z_j,z_k)(F) / F^2 <= 0.

The used indicators have the same pairwise covariance because each is one minus its unused indicator. Thus use of any two vertices on the three-vertex shore is negatively correlated under every such activity specialization. This is a statement about the probability measure on feasible endpoint supports, not the measure on individual matching witnesses.

## Redundant finite confirmation

Before finding the private-head argument, `universal_middle_check.py` independently localized all potentially negative middle-coefficient monomials. Three distinct exterior vertices give eight role types and 1,216 graphs; two exterior vertices with physical multiplicities 2,1 give fourteen types and 368 graphs. Every one of the resulting 22 role types and 1,584 graphs has nonnegative integer coefficient. These extra checks corroborate the corollary, but they are not needed once the private-head proof is established.

## Boundary of the result

This strengthens the previously proved Lorentzian theorem for a three-vertex physical shore, and gives coefficientwise inequalities rather than only scalar ULC. It still assumes that every arc crosses the core/exterior partition. Restoring arbitrary internal core arcs remains a separate problem. The Rayleigh variables here are the three core monomers; no Rayleigh assertion in the exterior variables or the role-activity variables is made.
