# An exact three-tail Lorentzian obstruction, including actual bipartite rank six

Status: proposed exact boundary note, submitted for independent review. October 1, 2026. Existing delivered releases are unchanged.

## 1. The proposed three-distinguished-element transform

Let M have rank q on an old set E and distinguished set P={A0,A1,A2}. Let Y be weighted heads with arbitrary nonempty neighborhoods in P. A triple (I,J,T), with I contained in E, J contained in P and T contained in Y, is feasible if there is K contained in J such that K matches perfectly to T and I union (J minus K) is a basis of M. Count the triple once, regardless of its allocations or matching witnesses. Define

  F_M^(3)(w,a,z)=sum_feasible w^I a^J (product_(y in T) v_y) z^(3-|T|).

It is homogeneous of degree q+3. This is the literal three-marked-element counterpart of the approved two-element transform. For an old nonloop e, differentiation in w_e gives the same transform for M/e, by restricting feasible triples to those containing e and deleting e; the Boolean existential allocation commutes with this restriction.

## 2. A real-representable rank-two counterexample

Take M of rank two on three parallel pairs {u_i,A_i}, i=0,1,2, with any pair from different classes independent. A real representation assigns directions (1,0), (0,1), and (1,1) to the three classes. Let Y consist of a private head for each A_i, each of weight p, and one common head of weight h.

In the derivative with all three distinguished variables selected,

  Q=partial_a0 partial_a1 partial_a2 F_M^(3)
   = R z² + B z(u0+u1+u2) + C(u0u1+u0u2+u1u2),

where

  R=3p+h,  B=2p²+3ph,  C=p³+3p²h.

Indeed a one-head subset leaves two distinguished basis elements and no old element, giving R. For an old u_i, a two-head subset must match a tail pair containing i; two private pairs and all three private/common pairs qualify, giving B. A three-head subset leaves two old basis elements; the three private heads or the common head with any two private heads qualify, giving C. No witness multiplicity appears.

After u0=u1=u2=x, the discriminant is

  (3B)²-4(3C)R = 3p²h(15h-4p).

Thus every p>15h/4 with h>0 gives a negative discriminant. At p=4,h=1,

  Q=13z²+44z(u0+u1+u2)+112(u0u1+u0u2+u1u2),

and its diagonal restriction is 336x²+132xz+13z², with discriminant -48. The two-dimensional Hessian [[672,132],[132,26]] is positive definite (determinant 48). Hence the original quadratic Hessian has at least two positive eigenvalues, so the three-element transform is not Lorentzian. Its full four-dimensional inertia is (2,2,0): the two sum-zero old-variable directions have eigenvalue -112.

This rank-two seed is not transversal. In any presentation, two parallel nonloops must both have the same singleton neighborhood; otherwise they could be matched to distinct slots. Three distinct nontrivial parallel classes would require three distinct singleton slots, yielding an independent triple, contrary to rank two. Representability alone therefore does not imply transversality.

## 3. A genuine bipartite graph of actual matching rank six

The nontransversal seed nevertheless occurs as an old-element contraction of a rank-three transversal seed. Use three slots q0,q1,q2, distinguished A_i and old dummies u_i private to slot i, plus one old element c adjacent to all slots. Contract c. Two elements from the same private class become parallel, two from different classes remain independent, and the contraction has rank two. It is precisely the matroid in Section 2.

Equivalently, take the following explicit bipartite graph. Its left shore is

  P union X = {p0,p1,p2} union {c,x0,x1},

and its right shore is

  Q union Y = {q0,q1,q2} union {y0,y1,y2,h}.

The only edges are p_i-q_i, p_i-y_i, p_i-h for i=0,1,2; c-q_i for i=0,1,2; and x0-q0, x1-q1. There are 14 edges. The displayed P union Q is a 3+3 vertex cover. A matching of size six is p_i-y_i (i=0,1,2), x0-q0, x1-q1, c-q2; since there are six left vertices, the actual matching rank is exactly six.

Give y0,y1,y2 activity 4, and every other vertex activity 1. Retain a separate selected variable for each left vertex. Define the natural degree-six homogenization

  F_G=sum_(S,T feasible) (product_(j in T) v_j)(product_(i in S) a_i)
          z^(3-|T intersect Y|) product_(j in Q minus T) z_j.

Differentiate in a_p0,a_p1,a_p2,a_c and then set a_x0=a_x1=0. The result is exactly Q from Section 2, in (z_q0,z_q1,z_q2,z). Its principal Hessian is

  [[0,112,112,44],
   [112,0,112,44],
   [112,112,0,44],
   [44,44,44,26]].

Thus a real bipartite graph of actual rank six fails this fully selected-tail multivariate Lorentzian property. This conclusion is obtained directly from endpoint supports, not by assuming the nontransversal seed itself has a graph presentation.

The scalar endpoint-support polynomial is

  Gamma(t)=1+23t+195t²+743t³+1234t⁴+744t⁵+112t⁶.

Its exact normalized Newton-gap numerators

  k(6-k) gamma_k² - (k+1)(7-k) gamma_(k-1)gamma_(k+1),  k=1,...,5,

are

  305, 47865, 1118361, 3890168, 1109184.

All are positive. This is not a scalar ultra-log-concavity counterexample.

## 4. Failure survives identifying all selected-tail variables

Use the same graph, but give p0,p1,p2,c activity L, give x0,x1 activity 1, give each private head y_i activity p, and give h and all Q vertices activity 1. Let H(t,x,z) be the homogenization after every left selected variable is replaced by its activity times t and every unused Q monomer is replaced by x.

Exact endpoint enumeration, or the three possible selected-Y cardinalities, gives

  [t^4]H=L²(A x²+B xz+C z²),

where

  A=L p²(3L+2)(p+3),
  B=p(6L²p+9L²+16Lp+32L+3p+6),
  C=3L²p+L²+10Lp+8L+5p+5.

Here A,B,C are local scalar names, unrelated to the distinguished elements. At L=100,p=8,

  [t^4]H/10000=21260800 x²+4688240 xz+258845 z²,

whose discriminant is -33412806400. If H were Lorentzian, its fourth t derivative followed by t=0 would be Lorentzian or zero; this nonzero quadratic instead has a positive-definite Hessian. Thus even the three-variable cover-order Lorentzian homogenization, with a single selected-tail variable, fails at 3+3. All activities here are positive, and the actual degree remains six.

The scalar coefficients at this second activity specialization are

  [1,3302,3846201,1806662900,262078850000,313024000000,70400000000].

The five corresponding integer gap numerators are

  [8361608,28862083622208,13248150548946090000,
   540999656224436000000000,268515910400000000000000],

again all positive. Neither example refutes scalar actual-rank-six ultra-log-concavity.

## Scope

The approved two-distinguished-element theorem has a sharp boundary for this particular multivariate generalization. The explicit graph also blocks its natural three-variable 3+3 analogue. No claim is made that scalar rank-six ULC fails, that all rank-six graphs have this obstruction, or that no different Lorentzian construction can prove a scalar theorem. The separate all-r first-layer PSD lemma remains valid and identifies a positive part of the higher-rank structure.
