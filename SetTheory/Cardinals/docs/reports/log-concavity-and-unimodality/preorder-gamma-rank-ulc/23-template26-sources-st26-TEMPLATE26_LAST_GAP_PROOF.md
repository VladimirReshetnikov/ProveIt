# A smaller proof of the last gap for template 26

Status: independently approved, including the deletion-mixture lemma, full support decomposition, top-ratio monotonicity, zero cases, and final square. The original degree-four theorem and its frozen certificate archive are unchanged. This is a certificate-assisted simplification, not a wholly ordinary proof.

## 1. The relation and support convention

There are three core/head vertices q0,q1,q2, with the single internal arc q2→q0, and a fourth core vertex p with all three arcs p→qi. Exterior vertices are independent. Every exterior vertex has an outgoing neighborhood in {q0,q1,q2}; if it contains q2, it also contains q0. Independently, p may point to that exterior vertex. Thus the possible exterior types, in bit order q0,q1,q2,p, are

1,2,3,5,7,8,9,10,11,13,15.

This is the canonical template with core rows [0,0,1,7] and orientation mask 8. A support is an ordered pair of disjoint equal-size subsets of the SAME physical vertex set admitting a directed perfect matching. It is counted once, not once per matching witness. All activities in this note are one.

Let Q be the induced preorder obtained by deleting p. Exterior vertices formerly adjacent only to p are now isolated. Ignore those isolates when recording the five other type populations (a,b,c,d,e), corresponding to neighborhoods 1,2,3,5,7. Write

Q(t)=1+A t+B t²+T t³.

Let H be the set of exterior vertices receiving an arc from p, including any Q-isolates. For each x∈H let Q_minus_x be the support polynomial after deleting that physical vertex. Define

R(t)=sum_(x∈H) Q_minus_x(t)=R0+R1 t+R2 t²+R3 t³.

Finally, Q_plus is Q with one new exterior tail adjacent to all three core/head vertices. This is a preorder: its universal outgoing neighborhood respects q2→q0. Its support polynomial has degree at most three; denote its quadratic and cubic coefficients by B_plus,T_plus.

## 2. Exact decomposition

Every support of the full template belongs to exactly one of two classes.

If its head set contains no exterior vertex, it is exactly a support of Q_plus, with the new universal tail identified with p.

If its head set contains an exterior vertex x, it contains exactly one such vertex: only p can match to exterior heads. The edge p→x is forced. Deleting the physical vertices p and x leaves exactly a support of Q_minus_x. Conversely, each such support, together with p→x, determines a full support. Different x give different head sets. This is a support-level bijection and introduces no matching multiplicity.

Therefore

Gamma(t)=Q_plus(t)+t R(t).                                      (1)

In particular,

Gamma2=B_plus+R1,  Gamma3=T_plus+R2,  Gamma4=R3.                 (2)

## 3. The deletion-average inequality

The independently approved deletion-mixture lemma establishes

R2²≥3 R1 R3.                                                  (3)

Its scope is the fixed five-type, one-internal-edge family Q above, with arbitrary nonnegative INTEGER type populations and arbitrary nonnegative coefficients in a mixture of Q and its one-exterior-vertex deletions. Identical deletion types are grouped. The Q-isolate deletions contribute Q itself. Hence R is within its scope.

The lemma uses the delivered vertex-weighted actual-degree-at-most-three theorem for the segments joining Q to Q_minus_x. Precisely, uQ+vQ_minus_x=(u+v)Q with the ONE distinguished physical vertex x assigned activity u/(u+v), for u+v>0. This is not a fractional-population substitution. If the degree drops below three, the last order-three inequality is trivial because the cubic coefficient vanishes. The zero polynomial is also harmless.

The remaining ten distinct-deletion pairs have exact quartic certificates, independently reconstructed from Hall support counts and checked coefficientwise. A two-point convex-hull lemma passes from segment safety to arbitrary nonnegative mixtures. See pair-compatibility/DELETION_MIXTURE_LEMMA.md and the independent deletion_mixture_approval_receipt.json. These finite identities are the certificate-assisted part of this proof.

## 4. Monotonicity of the top ratio with the internal edge restored

Let F be the exterior-only support polynomial on the three core/head vertices, obtained by removing q2→q0. Write B0=F2 and T0=F3. Let L be the number of exterior vertices adjacent to q1. Then, at support level,

B=B0+L,  T=T0.                                                (4)

Indeed, a size-two support using the internal arc must match its sole exterior vertex to q1; a size-three support cannot use the internal arc because only three core/head vertices exist.

Add one new exterior vertex of any outgoing neighborhood. Put

beta=Delta B0,  tau=Delta T0,  ell=Delta L∈{0,1}.

We claim

T_new B−T B_new = tau(B0+L)−T0(beta+ell) ≥0.                  (5)

First, the exterior-only terms satisfy

tau B0−T0 beta≥0.                                           (6)

For completeness, form the rank-three transversal matroid on the old exterior vertices, the new vertex x, and one private dummy for each core/head vertex. Its basis polynomial f counts feasible bases once. Wagner's theorem says every rank-three matroid is Rayleigh. Evaluate the Rayleigh inequalities for x and each private dummy at old exterior weights 1 and at x=dummies=0, using boundary continuity. At that point f=T0, f_x=tau, sum f_dummy=B0 and sum f_(x,dummy)=beta. Summing the three inequalities gives (6). The private dummies ensure the matroid has rank exactly three, even when the exterior-only graph has smaller matching rank.

Second, let K count exterior two-element supports matchable to the fixed pair {q0,q2}. Then

T0≤L K.                                                     (7)

To see this, choose a matching witness for each feasible exterior triple and record the vertex assigned to q1 together with the remaining two-element support. This is an injection into the pairs counted by L K: the recorded data determine the original triple. A choice of one witness suffices; multiple witnesses do not multiply the count.

If ell=1, adjoining the new vertex to any old support counted by K produces a distinct new feasible triple, by matching that vertex to q1. Consequently tau≥K, and

tau L−T0 ell≥LK−T0≥0.

If ell=0, the same expression is tau L≥0. Combining this fact with (6) proves (5). An added Q-loop gives equality. No division or positivity assumption is needed for (5).

Primary input: David G. Wagner, Rank–Three Matroids are Rayleigh, Electronic Journal of Combinatorics 12 (2005), N8, Theorem 1.1; https://arxiv.org/pdf/math/0403216 . The Rayleigh use is identical to the independently audited outward-star proof, while (7) handles the restored internal edge.

## 5. Compatibility with Q_plus

If R3=0, the desired last gap is simply 3 Gamma3²≥0. Suppose R3>0. Some Q_minus_x has a positive cubic coefficient, so Q has B>0 and T>0. For each x∈H write B_x,T_x for its quadratic and cubic coefficients.

Applying (5) first when x is restored and then when the universal vertex is added gives

T_x B≤B_x T,  T B_plus≤B T_plus.

The nonnegative factors give the chain

T_x B B_plus≤B_x T B_plus≤B_x B T_plus.

Cancel only the strictly positive B to obtain

T_x B_plus≤B_x T_plus.

This remains valid when B_x or T_x is zero, and Q-isolates give equality in the first step. Summing over x yields

R3 B_plus≤R2 T_plus.                                        (8)

## 6. The final square

Using (2), (3) and (8),

3 Gamma3²−8 Gamma2 Gamma4
=3(R2+T_plus)²−8(R1+B_plus)R3
≥ R2²/3−2R2 T_plus+3 T_plus²
=(R2−3T_plus)²/3
≥0.                                                        (9)

Thus the last order-four Newton inequality holds for every nonnegative integer population of template 26. Together with its separately approved middle-gap proof and the general first-gap bound, this gives a smaller proof of this family. It does not alter the original independently proved certificate or claim a new weighted degree-four theorem.
