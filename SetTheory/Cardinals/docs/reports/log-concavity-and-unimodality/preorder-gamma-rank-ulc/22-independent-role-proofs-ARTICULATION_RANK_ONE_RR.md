# An all-rank articulation theorem for role-weighted support polynomials

## Theorem

Let R be any finite directed relation without loops. Give each vertex strictly positive independent tail/head activities u_v,v_v. Suppose a vertex h has the property that every connected component of the underlying undirected graph of R-h has matching number at most one. Then the disjoint-support polynomial Gamma_R(z) has only real nonpositive zeros. In particular, its coefficients are ultra-log-concave with respect to their actual degree.

Transitivity is not required. Any number of residual components is allowed, so this is an all-rank statement. Zero activities follow by limits, with rank-ULC interpreted at the surviving degree.

## Support decomposition

Let C_1,...,C_m be the components after deleting h. Since each has matching number at most one, write

Q_i(z)=Gamma_(C_i)(z)=1+a_i z.

Every support of R[C_i union {h}] not already counted by Q_i uses h. Write its polynomial contribution as

P_i(z)=c_i z+d_i z^2.

There can be no degree-three term, since adjoining one vertex raises matching number by at most one. All a_i,c_i,d_i are nonnegative, and

d_i <= a_i c_i.

Indeed, a degree-two support counted by d_i admits an arc incident to h and a disjoint arc inside C_i. Their product weight is exactly the support weight. The product a_i c_i sums all pairs of a core arc and an h-incident arc, including every such support at least once, and possibly extra intersecting pairs or multiple witnesses. Thus the inequality is coefficientwise in the original role activities.

For the full graph,

Gamma_R = product_i Q_i + sum_i P_i product_(j!=i) Q_j.

To justify the sum without duplicate witnesses: a support not using h is a product of component supports. A support using h must pair it with one component. That component contributes an odd number of its own vertices; every other component contributes an even number. Thus the unique component with odd selected endpoint count determines the summand at support level, independently of the chosen matching witness. Conversely, the local support and the other component supports can always be combined.

## Direct real-rootedness proof

When a_i>0, division yields

P_i(z)/Q_i(z) = (d_i/a_i) z + (c_i-d_i/a_i) z/(1+a_i z),

and both coefficients are nonnegative. If a_i=0 then d_i=0 and P_i/Q_i=c_i z.

Let F(z)=1+sum_i P_i(z)/Q_i(z). For Im(z)>0,

Im(z/(1+a z)) = Im(z)/|1+a z|^2 > 0   for a>=0.

Consequently F either is identically 1 or has strictly positive imaginary part throughout the upper half-plane. It has no zero there. Each Q_i has no zero there either, so Gamma_R=(product Q_i)F has no upper-half-plane zero. Its coefficients are real, hence conjugation also excludes the lower half-plane. Its coefficients are nonnegative and its constant term is 1, so every zero is negative. This proves real-rootedness; Newton's inequalities give actual-degree rank-ULC.

The proof is an elementary support decomposition followed by the classical upper-half-plane criterion; no novelty priority claim is made.

## Consequence for weighted degree-three GE reduction

In the a=1 Gallai–Edmonds branch, pendant twins compress to one pendant with its relevant activity summed. A retained core of at most six vertices therefore reduces to a preorder on at most seven vertices. If the core has seven vertices, the GE rank budget forces its residual graph after deleting the sole attachment to consist of two matching-rank-one nontrivial components (two factor-critical triangles), and the exterior consists of rank-zero isolated components after deletion. The theorem applies directly, including arbitrary populations and independent activities. Thus a complete weighted theorem for all preorders on at most seven vertices would close the entire a=0 and a=1 branches.

This argument does not assert that adding pendants at arbitrary successive vertices preserves deletion interlacing. The hypothesis is checked once at the designated articulation vertex.
