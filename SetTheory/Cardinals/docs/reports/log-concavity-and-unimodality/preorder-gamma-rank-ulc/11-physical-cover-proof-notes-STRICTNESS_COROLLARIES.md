# Strict core negative correlation and equality in the cubic Newton inequality

Status: proposed ordinary corollaries of the approved coefficientwise three-core theorem, October 1, 2026. The released research packages are unchanged.

Throughout, D has physical bipartition C disjoint-union I with C={0,1,2}, and all arcs cross the partition. Fix nonnegative role activities. Delete every arc p→q with u_p v_q=0 and call the remaining relation D_+. Its underlying undirected graph is the positive-weight physical graph. Every positive support of D is a support of D_+ and conversely, with the same weight.

Use the approved notation a_i,b_ij,c and core-monomer polynomial F. Its Rayleigh differences satisfy

    Delta_(z_j,z_k)(F)
      = (a_j a_k - b_jk) z_i^2
        + (a_j b_ik + a_k b_ij - c - a_i b_jk) z_i
        + (b_ij b_ik - a_i c),

and all three activity-polynomial coefficients are nonnegative.

## Strictness of negative correlation

Give supports probability proportional to u^S v^T times the product of strictly positive core monomer activities over unused core vertices. For distinct core vertices j,k:

- Their used (and unused) indicator covariance is strictly negative if j,k are in the same connected component of the underlying graph of D_+
- The covariance is zero if they are in different components

### Proof

If they are in different physical components, endpoint supports and weights factor uniquely across components. The corresponding support distributions are independent, so the covariance is zero; equivalently the core polynomial factors and Delta_(z_j,z_k) is zero.

Suppose they are connected. A simple alternating physical path between them has length two or four, since C has only three vertices.

For a path j−x−k of length two, choose a positive directed orientation available on each of its edges. Their two single-edge supports contribute a positive monomial to a_j a_k in which x has physical multiplicity two. No term of b_jk has that monomial, because a size-two support uses two distinct exterior physical vertices. Hence a_j a_k−b_jk is strictly positive at the specified activities. Since z_i>0 and the other two Rayleigh coefficients are nonnegative, Delta_(z_j,z_k)>0.

For a path j−x−i−y−k of length four, x and y are distinct. The two disjoint-edge supports {j−x,i−y} and {i−x,k−y}, with positive available arc directions, contribute a positive monomial to b_ij b_ik using only the two exterior vertices x,y. No term of a_i c uses only two exterior physical vertices, because c requires three distinct exterior vertices. Therefore the boundary coefficient b_ij b_ik−a_i c is strictly positive at the activities. The other Rayleigh coefficients are nonnegative, so Delta_(z_j,z_k)>0 again.

In both constructions, the formal monomial may use one physical vertex in different roles across its two factors; this is permitted in a polynomial product. Each individual support is physically disjoint. Because all selected arcs belong to D_+, its monomial evaluates positively. The coefficientwise theorem prevents cancellation by other negative coefficients.

Finally Cov(unused_j,unused_k)=−z_j z_k Delta_(z_j,z_k)/F², with all three denominator/prefactor quantities positive. This gives strict negativity. Used indicators have the same covariance.

## Equality in the upper cubic Newton inequality

Assume the actual support degree is three, equivalently c>0. Write Gamma=1+At+Bt²+ct³ with A=sum_i a_i and B=sum_(i<j)b_ij. Then

    B²=3Ac

if and only if, after zero-weight arcs and isolated vertices are discarded, the positive-weight physical graph is a disjoint union of three stars, each centered at one core vertex, and their total directed arc activities are equal. In that case

    Gamma(t)=(1+at)³

for their common positive arc-activity total a.

### Proof

The approved exact identity is

    B²−3Ac
      = 1/2 [(b_01−b_02)²+(b_01−b_12)²+(b_02−b_12)²]
        +3 sum_i (b_ij b_ik−a_i c).

All summands are nonnegative, so equality forces all three b_ij to agree and all three boundary gaps to vanish.

We show that if any exterior vertex x is adjacent to at least two core vertices in D_+, some boundary gap is strictly positive. Suppose first x is adjacent to j,k and the remaining core i has a neighbor y different from x. The two supports {i−y,j−x} and {i−y,k−x} contribute a positive monomial to b_ij b_ik with only exterior vertices x,y. The negative term a_i c cannot contain it. Thus that boundary gap is strictly positive.

If the remaining core i has no neighbor other than x, then x is adjacent to all three cores. A matching saturating C exists because c>0; it must use i−x and must match j to some y different from x. Use j as the doubled core and use the shared neighbor x for the other two cores. The preceding two-support construction again gives a strictly positive boundary gap.

Therefore equality permits no shared exterior neighbor. The positive-weight physical graph is a disjoint union of the three stars centered at the core vertices, plus irrelevant isolates. With no exterior vertex shared by different cores, supports factor, so

    b_ij=a_i a_j,       c=a_0 a_1 a_2,
    Gamma(t)=product_i (1+a_i t).

Here each a_i is positive because c>0. Equality of b_01,b_02,b_12 therefore forces a_0=a_1=a_2=a. Conversely these three equal star totals give Gamma=(1+at)³ and equality in the displayed Newton inequality.

Opposite arcs on a star edge simply contribute two distinct singleton supports, with their respective role activities, to its total a_i. They do not affect the proof.

## Scope

These statements use positivity in the actual active relation D_+, not merely the presence of a zero-weight arc in D. No conclusion is drawn about strictness in a relation with internal physical core arcs. The equality characterization is for actual degree three; it does not silently apply cubic normalization after a degree drop.
