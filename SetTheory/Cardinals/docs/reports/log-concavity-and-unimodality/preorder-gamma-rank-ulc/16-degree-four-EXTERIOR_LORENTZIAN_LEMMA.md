# Exterior-only supports are Lorentzian at the core-cover order

## Statement

Let P and Q be disjoint finite sets, and I a finite set of physical exterior
vertices. Give arbitrary arcs P→I and I→Q, with no other arcs. An exterior vertex
may have both incoming and outgoing neighbors, but matching supports always use
ordered DISJOINT endpoint sets. Let F_k count supports of size k, once per support.
Put r=|P|+|Q|. Then

H(z,t)=sum_{k=0}^r F_k z^(r-k)t^k

is Lorentzian. The statement also permits independent nonnegative activities for
using each exterior vertex as a head or as a tail. In particular, at r=4,

3 F1²≥8 F0 F2, 4 F2²≥9 F1 F3, and 3 F3²≥8 F2 F4.

This is an order-r statement for arbitrary r=|P|+|Q|. When deg(F)=r it is actual-degree ULC. When deg(F)<r, it asserts only the weaker binomial-order-r inequalities, not actual-degree ULC. No division by a common power of z is used or justified.
It does not assert real-rootedness when one side has rank at least three.

## Exact matroid construction

For the P side, make a rank-|P| transversal matroid M_P. Its ground set consists
of I and distinct private dummy elements d_p, one for every p∈P. The bipartite
presentation has right vertex set P; physical exterior i is adjacent to its P
neighbors, and d_p is adjacent only to p. All private dummies form a basis, so the
rank is exactly |P|, including when some physical exterior vertices are loops.

A ground-set subset R∪{d_p:p∈P\P′} is a basis precisely when |R|=|P′| and the
physical set R can be matched into P′. Thus a basis specifies the physical exterior
head support R and the used core support P′ uniquely. It is counted once regardless
of how many bijective matchings realize it.

Let B_P(x,u) be the ordinary squarefree basis-generating polynomial of this matroid.
Construct M_Q and B_Q(x,v) analogously, using distinct private dummy variables and
the SAME physical variables x_i for I. A basis on the Q side specifies the
physical exterior tail support L and its used core support Q′.

Both basis polynomials are Lorentzian, and their product is homogeneous of degree
r. In the product, a physical vertex used on both sides has exponent two in x_i.
Apply the coordinate upper truncation x_i-degree≤1 for every physical vertex.
The truncation removes exactly those overlapping choices and changes no surviving
coefficient. The product remains nonzero because the all-dummy term survives.

Now substitute every dummy variable by z and every physical variable by t. A
surviving pair of bases with |L|+|R|=k contributes z^(r-k)t^k. Its data
(P′,Q′,L,R) specify exactly the directed matching support

A=P′∪L, B=Q′∪R.

The external injections on the two sides are independent, and L∩R=∅ is exactly the
physical disjointness condition. Consequently the resulting polynomial is H.
All operations preserve homogeneity of degree r. No homogenizing monomial is ever
divided out.

For role activities, multiply x_i by the head activity in B_P and by the tail
activity in B_Q before forming the product. These are nonnegative substitutions;
the same argument applies.

## Sources and normalization

Brändén–Huh, *Lorentzian polynomials*, Annals of Mathematics 192 (2020), Theorem3.10,
identifies matroid basis-generating polynomials as Lorentzian. Its exponential
normalization causes no extra factors here because every basis exponent is0 or1.
Primary text: https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf

Ross–Süss–Wannerer, *Dually Lorentzian Polynomials*, Monatshefte für Mathematik208
(2025), Theorem3.1 gives products and nonnegative linear substitutions; Proposition3.3
gives the coordinate upper truncation used above. These statements were checked in
the primary text: https://link.springer.com/article/10.1007/s00605-025-02134-6

For r=4 the binary Lorentzian Hessian conditions give the displayed constants
directly. The derivative ∂t²H is 2F2 z²+6F3 zt+12F4 t², whose discriminant is
nonnegative, yielding 3F3²≥8F2F4. The mixed derivative ∂z∂tH is
3F1 z²+4F2 zt+3F3 t², yielding 4F2²≥9F1F3. The remaining derivative gives the first
inequality. Thus no factorial or binomial normalization is being silently changed.

## Use in the four-core problem

For any four-attachment template, split core vertices according to their fixed
exterior orientation into P and Q, and delete all core arcs. The resulting
exterior-only polynomial F satisfies the lemma, irrespective of whether that
edge-deleted relation is itself transitive.

In the original four-core preorder, gamma4=F4, gamma3=F3+C and gamma2=F2+B, where
C counts supports using two exterior vertices and one core edge, and B counts
supports using zero or one exterior vertex. Both are nonnegative counting
polynomials in integer populations. Therefore

3 gamma3²−8 gamma2 gamma4
=(3 F3²−8 F2 F4)+(6 F3 C+3 C²−8 B F4).

The first parenthesis is proved nonnegative by this lemma. The core-correction
parenthesis still requires a separate argument; its sign is NOT asserted here.
