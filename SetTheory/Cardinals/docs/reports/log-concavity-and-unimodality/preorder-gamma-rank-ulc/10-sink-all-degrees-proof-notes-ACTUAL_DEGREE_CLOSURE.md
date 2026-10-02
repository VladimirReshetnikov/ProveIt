# Rank ultra log concavity at every surviving degree

## New stronger coefficient theorem

For the unchanged universal-sink family (an arbitrary loopless directed four-core and an arbitrary finite independent set of universal sinks), with arbitrary independent nonnegative tail/head activities, the complete exact certificate collection proves

    gamma_2^2 >= 3 gamma_1 gamma_3.

This is stronger than the degree-four middle inequality, and is valid with any number of sink heads, including zero activities. It therefore closes the actual-degree-drop boundary directly, without needing the earlier role-matching-rank-at-most-three theorem as a dependency.

The support coefficients remain

    gamma_1=a+e_1E_1,
    gamma_2=b+cE_1+e_2E_2,
    gamma_3=dE_2+e_3E_3,
    gamma_4=e_4E_4.

The same sharp moment reduction applies: A=sqrt(sum w_x^2), B=sum w_x-A>=0,

    E_1=A+B,
    E_2=AB+B^2/2,
    E_3<=AB^2/2+B^3/6.

The cubic gap gamma_2^2-3gamma_1gamma_3 decreases with E_3. In the same ten-variable order as before, G_1=gamma_1, G_2=2gamma_2, G_3=6gamma_3 at the boundary triple, so the new integer target is

    Q_H = G_2^2-2G_1G_3 = 4(gamma_2^2-3gamma_1gamma_3).

Every one of the 218 directed isomorphism classes has an exact nonnegative-orthant certificate. There are 3532 positive rational weighted monomial multiples of polynomial squares, plus 64298 positive remainder monomials. Of the 218 certificates, 127 use binomial squares only and 91 also use larger square polynomials. A square may have between 2 and 24 monomials. The complete independent verifier reconstructs Q_H from Boolean support data, expands every rational square, checks every remainder coefficient, and covers all 4096 labeled loopless cores.

## Actual-degree first coefficient inequality

For any finite loopless directed relation with nonnegative independent role activities, remove arcs whose product activity is zero. This does not remove a physical vertex from its other role. Let d be the actual degree of its support polynomial. If d>=2, then

    (d-1) gamma_1^2 >= 2d gamma_2.

Proof: form an undirected graph L whose vertices are the remaining directed arcs and whose edges join arcs with disjoint physical endpoint sets. Give arc i→j weight u_i v_j. A clique of size k is precisely a positive-weight physical matching of size k, so L has clique number d. Also gamma_1 is the sum of all arc weights, and gamma_2 is bounded above by the sum of products over edges of L, because every feasible size-two support has a witness of exactly its support weight.

The weighted Motzkin–Straus bound for a graph of clique number d is

    sum_(ab edge) x_a x_b <= (d-1)/(2d) (sum_a x_a)^2.

A self-contained proof proceeds by mass shifting. If positive coordinates a,b are nonadjacent, fix their sum and move all of it to the coordinate with the larger weighted neighbor sum. The edge quadratic is affine in that split, so it does not decrease. Each move reduces the number of positive coordinates. Eventually they lie on a clique of size q<=d. On that clique the quadratic is ((sum x)^2-sum x^2)/2, at most (q-1)/(2q)(sum x)^2 by Cauchy, and hence at most (d-1)/(2d)(sum x)^2. This proves the bound and the first coefficient inequality.

This is the classical Motzkin–Straus argument, applied to the graph of physically disjoint arcs. Primary original paper, checked on 2026-10-01: T.S. Motzkin and E.G. Straus, Maxima for graphs and a new proof of a theorem of Turan, Canadian Journal of Mathematics17 (1965),533–540, Theorem1. https://doi.org/10.4153/CJM-1965-053-6 . Original PDF: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/S0008414X00039493 . No novelty is asserted for this bound.

## No padded normalization

The universal-sink family has at most four possible tails, so its actual degree d is in {0,1,2,3,4}. Whenever its top coefficient is positive, taking submatchings of a positive-weight support shows that every earlier coefficient is positive too.

- d=0 or1: rank-ULC has no nontrivial inequalities
- d=2: the actual-degree first inequality gives gamma_1^2>=4gamma_2
- d=3: the actual-degree first inequality gives gamma_1^2>=3gamma_2; the newly certified cubic inequality gives gamma_2^2>=3gamma_1gamma_3
- d=4: the actual-degree first inequality gives3gamma_1^2>=8gamma_2; the cubic inequality implies4gamma_2^2>=9gamma_1gamma_3; the ordinary universal-sink last-gap proof gives3gamma_3^2>=8gamma_2gamma_4

Thus rank-ULC holds at every actual surviving degree, with zero activities treated directly. This statement includes nontransitive directed cores and every preorder core. It does not concern non-universal exterior neighborhoods or larger cores, and makes no real-rootedness claim.

## Relation to the initially proposed boundary split

The alternative zero-tail argument is valid: after deleting zero-weight arcs, at most three active tail roles imply role-matching rank at most three. Vertices with zero tail activity must remain available as heads. The previously proved arbitrary-relation role-rank theorem then applies at actual degree. However, this observation is not required by the stronger all-cloud cubic theorem proved here. Likewise, no finite-three-sink certificate is needed for the final proof. Exploratory sorted-three-sink calculations are omitted from the deliverable.

Earlier approved archives remain unchanged. The new result is a genuine strengthening, established by new exact certificates; it is not obtained by renormalizing the old degree-four inequalities.
