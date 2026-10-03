# Stable physical monomers for empty or star two-by-three cores

Status: proposed ordinary theorem, review pending. Frozen releases are unchanged.

## Statement

Let a bipartite graph have shores P union X and Q union Y, with |P|=2, |Q|=3, complete exterior blocks P x Y and X x Q, and an arbitrary internal core H subset P x Q. Suppose nu(H)<=1. Then, with arbitrary independent nonnegative vertex activities, its signed physical support-monomer polynomial is real stable. In particular the support polynomial has only negative real zeros and is ULC at its actual degree, including zero-activity degree drops.

This covers H empty and all stars centered on either core shore. It does not assert stability for matching-two cores; the approved full-core example already has nonreal roots.

## Stable seed transfer

For a bipartite graph with a fixed head side Q, adjoin one private dummy d_j to each head slot j. Form the transversal matroid on the tail vertices and these dummies, whose bases encode selected tail sets, selected head sets, and unused head dummies. The basis polynomial counts each endpoint support once.

If this basis polynomial B is real stable, the signed physical monomer polynomial is stable. For positive activities, the exact transformation is

 mu(a,b)=(product_tail a_i)(product_head v_j)
          B(x_i=-u_i/a_i, d_j=b_j/v_j).

Each transformed argument remains in the upper half-plane; the prefactors do not vanish there. Coefficientwise limits give nonnegative activities. This is the seed part of the previously approved pendant-head theorem, with no uncovered heads. The all-unused monomial excludes the zero polynomial.

A complete bipartite graph has uniform dummy matroid: every subset of ground elements of the required head-side cardinality is a basis. Its basis polynomial is elementary symmetric and is real stable. The same holds for a single exceptional tail whose nonempty head neighborhood is a singleton: it is parallel to the corresponding private dummy, so the basis polynomial is elementary symmetric after a nonnegative linear substitution. These elementary-symmetric seed cases are already approved.

## One exceptional two-neighbor tail with three heads

Let the head side have three vertices, every tail in X be universal, and one extra tail p be adjacent to precisely two heads, say 1 and 2. The dummy matroid has rank three on X union {p,d_1,d_2,d_3}. Every three-subset is a basis except {p,d_1,d_2}: this is immediate from the three-slot matching condition, since all X elements are universal and d_j is private to slot j.

Write L0={p,d_1,d_2} and O=X union {d_3}, with |O|=m>=1. Its basis polynomial is

    B=e_3(L0 union O)-p d_1 d_2.

It is multiaffine and symmetric separately in L0 and O. On the two-block diagonal it becomes

    B(x,x,x;y,...,y)
      = y[3m x^2+3 binom(m,2)xy+binom(m,3)y^2].

The quadratic in brackets has nonnegative coefficients, positive x^2 coefficient, and discriminant

    9 binom(m,2)^2-12m binom(m,3)
      =m^2(m-1)(m+7)/4 >=0.

It therefore factors into real linear forms with nonnegative coefficients; together with y it is real stable. The cases m=1 or 2 simply have zero coefficients at the high y powers and cause no problem.

Polarizing the x and y variables recovers exactly B. Stability of polarization is Borcea--Branden, *The Lee--Yang and Polya--Schur programs I*, Proposition 2.4 (arXiv:0809.0401, printed page 11). Hence B is stable. This is the only extra seed needed here.

Primary theorem source: https://arxiv.org/pdf/0809.0401 . The polarization definition and proposition apply with degree bounds (3,m); equality with the actual degree in each variable is not required.

Combining this with the empty, singleton, and universal exceptional neighborhoods proves stability for a three-head graph consisting of any number of universal tails and one arbitrary exceptional tail.

## One-vertex gluing

Suppose two directed physical relations meet in exactly one vertex p and have no other cross edges. Give the shared vertex the same role activities in both pieces. Let their stable signed monomer polynomials use separate copies a,b of the shared unused-vertex monomer. Their product is multiaffine in a,b, say

    f=Aab+Ba+Cb+D.

A physical support cannot use p in both pieces. The exact gluing map is

    ab -> z_p, a -> 1, b -> 1, 1 -> 0,

so the resulting monomer polynomial is A z_p+B+C. This counts endpoint supports, not matching witnesses: if p is used, the tail/head imbalance among the other selected endpoints in each piece uniquely determines the piece containing its matched edge. If p is unused, both restricted supports exclude it.

The map preserves stability, since

    A z_p+B+C = [partial_t f(t,t)]_(t=z_p/2).

Diagonal substitution, differentiation, and positive scaling preserve real stability or zero; the all-unused monomial excludes zero. This is also the previously approved physical merge operator.

## Apply the gluing

A nonempty bipartite graph of matching number one is a star. If H is centered at p in P, split the full graph into the complete bipartite piece on P union Y and the piece on {p} union X union Q. The latter has three heads, universal tail set X, and the one exceptional tail p. Both pieces have stable monomers by the preceding seeds; their intersection is exactly p. Gluing proves the claim.

If H is centered at q in Q, split into the complete bipartite piece on X union Q and the piece on P union Y union {q}. The latter has a two-vertex fixed tail side, universal opposite vertices Y, and one exceptional opposite vertex q. After reversing the roles of the two shores, its dummy matroid has rank two and only singleton or universal neighborhoods. The approved elementary-symmetric seed theorem applies. Glue at q.

If H is empty, use the product of the two disjoint complete bipartite pieces.

Finally, diagonalizing the signed monomer polynomial on all physical vertices yields x^n Gamma(-x^(-2)). Real stability gives a real-rooted diagonal; because Gamma has constant term one and nonnegative coefficients, every zero of Gamma is negative real. Newton's inequalities then give actual-degree ULC. This conclusion survives zero activities without needing a padded degree-five normalization.

## Remaining masks

There are 18 labeled two-by-three core masks of matching number at most one: the empty mask, six single edges, six two-edge stars centered on P, two three-edge stars centered on P, and three two-edge stars centered on Q. Up to independent permutations of P and Q, these form five types. The full set has thirteen such isomorphism types; after these five types and the separately approved full core, seven noncomplete matching-two types remain.
