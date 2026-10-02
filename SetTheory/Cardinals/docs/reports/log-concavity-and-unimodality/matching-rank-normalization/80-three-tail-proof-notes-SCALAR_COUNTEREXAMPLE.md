# Weighted bipartite support ULC fails at every actual rank at least six

Status: proposed ordinary theorem and exact counterexample, submitted for independent review. October 1, 2026.

## 1. Complete three-block graphs and exact support counting

Let the bipartite shores be P union X and Q union Y, all four sets disjoint. Let |P|=p, |Q|=q, |X|=m, |Y|=n. Include exactly all edges of P×Q, P×Y and X×Q. Assign every core vertex in P union Q the positive activity lambda, and every exterior vertex activity 1. Let gamma_k count feasible endpoint supports (S,T) of size k once, weighted by the product of activities of their endpoints.

For a support selecting i core tails from P and j core heads from Q, it selects k-i vertices of X and k-j vertices of Y. It is feasible exactly when i+j>=k. Necessity follows because X can only match Q and Y can only match P. For sufficiency, first match the selected X vertices to distinct selected Q vertices and the selected Y vertices to distinct selected P vertices. The remaining selected P and Q populations both have size i+j-k, and the complete core matches them.

Therefore the exact coefficients are

  gamma_k = sum_(0<=i<=p, 0<=j<=q, i+j>=k)
       binom(p,i)binom(q,j)lambda^(i+j)
                binom(m,k-i)binom(n,k-j),             (1)

where out-of-range binomial coefficients are zero. This counts each endpoint pair once, not each perfect matching.

If m>=q and n>=p, the actual matching rank is d=p+q: P union Q is a cover of size d, and matching all P into Y and all Q into X gives d edges. All activities are strictly positive, so the surviving degree is exactly d.

## 2. An explicit rank-six counterexample

Set p=q=3, m=n=N. Put A=binom(N,2), B=binom(N,3). The top coefficients from (1) are

  gamma_6=lambda^6 B²,
  gamma_5=lambda^5(lambda A²+6AB),
  gamma_4=lambda^4(lambda²N²+6lambda NA+9A²+6NB).

Thus the last degree-six Newton gap has the exact factorization

  5gamma_5²-12gamma_4gamma_6
    =lambda^10 N^4(N-1)²/48 * T_N(lambda),            (2)

where

  T_N(lambda)=(-N²+34N-49)lambda²
       +12(N-1)(N-2)(N+3)lambda
       +8(N-1)(N-2)²(N+1).                           (3)

The leading coefficient is negative exactly when N>=33 among integers N>=3, since its positive root is 17+4sqrt(15). Hence for every N>=33, sufficiently large finite core activity violates the last Newton inequality.

Choose N=40, lambda=10000. The graph has 86 vertices, a six-vertex cover and a size-six matching. To keep coefficients compact, rescale the variable: write g_k=gamma_k/lambda^k, so sum g_k t^k=Gamma(t/lambda). Its exact coefficient sequence is

  [1,90240,907219080,1024191381360,
   161879846800,6130238400,97614400].

The last gap is

  5g_5²-12g_4g_6 = -1722535205514240000 < 0.           (4)

A positive variable rescaling multiplies each Newton gap by a positive factor, so (4) disproves actual-degree ULC for the original weighted graph as well.

A smaller member of this symmetric family uses N=33, lambda=30000, with 72 vertices. Its scaled coefficients are

  [1,270198,8117832969,27178589394544,
   983239909344,8380804608,29767936],

and its last gap is -38842940605759488. No overall minimum-vertex claim is made. The first four degree-six gaps are positive in both displayed examples; failure is at the last interior index.

## 3. Counterexamples in every actual rank d>=6

Fix any p,q>=3 and d=p+q. For fixed exterior sizes m>=q,n>=p, the leading core-activity terms of (1) satisfy

  gamma_(d-j)/lambda^d -> binom(m,q-j)binom(n,p-j),
                      j=0,1,2, as lambda -> infinity.

Only i=p,j=q contributes this leading power. Consequently the limiting top-coefficient ratio, followed by m,n -> infinity, is

  gamma_(d-1)²/(gamma_(d-2)gamma_d)
           -> [q/(q-1)] [p/(p-1)].                  (5)

More explicitly, before the exterior-size limit the ratio is

  [q/(q-1)] [(m-q+2)/(m-q+1)]
       * [p/(p-1)] [(n-p+2)/(n-p+1)].

The last rank-d ULC inequality requires this ratio to be at least 2d/(d-1). For p,q>=3,

  2d(p-1)(q-1)-pq(d-1)
     =(d+1)pq-2d(d-1)
     >=3(d+1)(d-3)-2d(d-1)
     =d²-4d-9>0.

Thus the limit (5) is strictly below the required bound. First choose finite m,n large enough to retain the strict inequality, then choose a finite positive lambda large enough. The graph still has actual rank d. Taking p=3,q=d-3 gives a weighted counterexample for every d>=6. This is an ordinary limiting-existence argument with strict margins, not an inference from numerical search.

## 4. Sharpness and height-two orders

The already approved all-matroid two-element paper, Corollary 5.2, proves actual-degree ULC for every independently nonnegative vertex-weighted finite bipartite graph of surviving rank at most five. Its frozen package and readable PDF are included as a dependency in the forthcoming integrated release. Combined with Sections 2-3, five is the exact largest universal weighted matching-rank threshold: the guarantee holds through five and fails in every rank six and above.

Orient every edge of the counterexample from the left shore to the right shore. This is a height-two strict partial order, because no two nontrivial oriented edges compose. Adding reflexive pairs gives a preorder with the same disjoint-endpoint supports: a loop cannot be used when S and T are disjoint. Assign to each physical vertex the same activity used above. Therefore the counterexamples already occur for vertex-weighted height-two orders/preorders. Independent tail/head activities are not needed for the failure.

The counterexamples are weighted. No unweighted counterexample or universal failure statement for every graph at rank six is claimed. The previously approved multivariate obstruction examples have strictly ULC scalar polynomials; those remain useful separate boundaries, but scalar rank-six ULC is now refuted by the complete-block examples in this note.
