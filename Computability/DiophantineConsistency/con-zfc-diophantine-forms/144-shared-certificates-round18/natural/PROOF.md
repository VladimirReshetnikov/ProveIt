# Pooled digits in the aligned self-sized radix

## 1. Statement and inherited interface

All unknowns in this component range over the nonnegative integers. The input is the literal 334-variable, 284-row normalized quadratic graph `source/equation.json` of Round17 `architecture/strict_natural229/raw`. Its ordinary unbounded equivalence to a finite C222 derivation is retained in `proofs/ONE_ROW_SEMANTIC_ANCHOR_PROOF.md`; the named C222/ZF and ZF/ZFC refutation interfaces are inherited, not newly kernel-checked. The present changes replace only eleven private remainder bounds, and in one variant the exact-binomial output bound. No other raw arithmetic row changes.

Every displayed output is the sum of the squares of its complete listed quadratic residuals. The fully collected quartic is separately materialized. Thus its zero set is precisely the simultaneous zero set of those residuals. Our result is a ZFC-formalizable ordinary proof that each new equation has a natural zero iff the parent does iff ZFC has a finite refutation. It does not prove consistency or inconsistency, assert a global optimum, or supply a fresh end-to-end proof-assistant certificate.

Use the parent's notation: t>=12, F=t! in completed witnesses, B=binom(F²+t,t), V0=(F²+1)^t, K=x, N=B^K. Let S=1+C+sum(eight encoded columns) be the positive representative sum (not the separately named stack representative). The self-sized radix is q=(N*S)^K. Its six exact powers, the full anchor at J, and the simultaneous Pell-index row remain byte-for-byte unchanged. The four denominator families are

| Labels | Denominator |
|---|---|
| exact factorial binomial `choose0`, and C (`crt.range.index`) | D0=q^t |
| a,b,c,d,J | D1=q^(t+1)=q*D0 |
| stack representatives S0,S1 (`crt.range.S`, `crt.range.Sp`) | Dy=q^(y+1) |
| quotient representatives u,v (`crt.range.u`, `crt.range.vq`) | Dx=q^x |

There are eleven remainders r_i. The original separate bounds are D_i=r_i+s_i+1 with s_i>=0. The exact binomial additionally has q=B+o+1.

## 2. General coefficient-budget lemma

Let q>=2, k>=1, and let r_i=sum_{j=0}^{k-1} c_{ij}q^j with nonnegative integer coefficients. If sum_i c_{ij}<=q-1 for each j, then sum_i r_i<=q^k-1. Consequently the single bound q^k=sum_i r_i+s+1 has a natural slack. Conversely that bound, for arbitrary natural r_i and s, implies every r_i<q^k, and the old private slacks are restored by

    s_i = s + sum_{h != i} r_h.

The inequality needed for completeness concerns the sum of the coefficients, not just the old separate inequalities. We prove it for the actual self-sized radix next.

## 3. A uniform margin for the actual radix

Construct completeness witnesses by the parent's prescribed order. Start with a finite derivation, pad t>=12, set F=t!, B, K=x, N=B^K, and choose all nine independent positive CRT representatives modulo N². Lift a by N², preserving every required congruence. Thus the sum S satisfies S>N², and each independent representative is strictly less than S. The unchanged endpoint inequalities give K=x>=F+1>=2, and the inherited factorial bootstrap gives B>F>=1. Hence N>=4 and

    q=N^K*S^K >=16*S^K.

For an ordinary representative n<S and every requested lower position 0<=j<=k<=K,

    binom(n,j) <= max(1,n^K) < S^K.

For the derived label J, the inherited positive-DAG majorant gives J<=S^ell with ell=2^22. The parent's factorial inequality ell(t+1)<F<K gives, at all positions j<=t+1,

    binom(J,j) <= max(1,J^j) < S^K.

For the factorial upper index F²+t, the parent's elementary binomial bound gives binom(F²+t,j)<=V0 for 0<=j<=t. Its ceiling bootstrap proves V0<B²<=N. Since S>N², both V0 and B are strictly below S^K. Therefore every low-digit coefficient used here, and also B, is at most S^K-1.

All these are completeness estimates, after genuine semantic witnesses have been fixed. They do not assume the factorial identity prematurely in soundness. The old Pell output equations then supply exactly the canonical low base-q residues: the unchanged common-root identity identifies (q+1)^n modulo the relevant digit modulus, and every coefficient through the requested position is below q. No exponentiation primitive is added to a final polynomial.

## 4. Four pooled bounds

For each of the four groups replace all its old private bounds by

    D_G = sum_{i in G} r_i + s_G + 1.                 (P4)

The largest group has five terms. In each low position its coefficient sum is at most 5(S^K-1)<q. Section2 supplies each new natural slack. The four pools replace eleven rows/slacks by four, deleting seven variables and seven rows in the normalized raw graph (334/284 becomes327/277).

For soundness, every old bound is recovered by the explicit nonnegative-polynomial restoration in Section2. All other source variables and rows are untouched, yielding a zero of the exact parent graph. There is no appeal to binomial semantics to establish this direction, so no circularity. For completeness, first construct the parent's true witnesses from a refutation as in Section3, then use the coefficient lemma for the four new slacks. This is equivalence of existence; arbitrary parent zeros are not claimed to carry uniquely to new zeros.

## 5. A weighted three-pool variant

The equality D1=qD0 permits the first two groups to share one bound. Write r0,rC for the two D0 remainders, and T=r_a+r_b+r_c+r_d+r_J. Replace their seven bounds by

    qD0 = q(r0+rC)+T+s+1.                            (P3)

The Dy and Dx pools remain as in (P4). Soundness follows from q>=1 and D0>=1: the row gives q*r0<qD0 and q*rC<qD0, hence r0,rC<D0; it also gives every term of T<D1. All old private slacks are the integer polynomials D_i-r_i-1 and are nonnegative by these inequalities. Their substitution makes every deleted old bound identically zero.

For completeness, multiplication by q shifts each small remainder's digit coefficients by one position. All resulting terms have positions below t+1. At any position at most seven original low coefficients contribute, so the sum is at most7(S^K-1)<q. The coefficient-budget lemma gives s>=0. This variant has326 raw variables and276 rows.

The soundness use of q>=1 is licensed before factorial or binomial decoding: the retained Pell frame and anchor identify the six exact powers first; the unchanged ceiling equations give B>=1, V0>=1, F>=1, B>F, and K>=2, so N=B^K>=4 and q=(NS)^K>0. This is exactly the parent's noncircular bootstrap, which does not use any removed remainder bound or exact digit-output bound.

## 6. Absorbing the exact output bound

One can additionally replace (P3) by

    qD0 = q(r0+rC)+T+B*D0+s+1                       (P3B)

and delete q=B+o+1 and its private o. Its term B*D0 has position t. At every position at most eight quantities bounded by S^K-1 contribute, so their sum is below8S^K<=q/2<q; completeness again follows from Section2. All rows remain quadratic: q*r_i and B*D0 are products of existing coordinates, not new gates.

For soundness, the same inequalities restore all eleven old remainder bounds. The new row also gives B*D0<qD0; D0>0 implies B<q. Thus o=q-B-1 is a nonnegative integer and restores the exact output bound. Its bootstrap is valid in the order stated in Section5. The new raw graph has325 variables and275 rows. This absorption is a new composable strengthening of the pooled-digit method, not a claim that the unpublished exploratory strategy present in an incoming source was already proved there.

## 7. Exact nonnegative projection

Each output is obtained from its raw source by a finite sequence of monic integer polynomial substitutions. Every restored coordinate is certified as a positive rational combination of squares of affine rational forms plus a polynomial with nonnegative integer coefficients. This is nonnegative for every tuple in the natural domain. The independent checker expands every certificate exactly, checks its equality to the integer restoration polynomial, replays every substitution and retained row, verifies all residuals remain quadratic, and independently expands the complete sum of squares.

Reordering rows changes no system. Any selected projection order is shipped as an explicit finite row-order list, and both its permutation property and exact relation to the unchanged pooled source are verified. No heuristic ordering or finite numerical test is used as a proof of the unbounded equivalence.

Combining the raw soundness/completeness maps with the certified projections proves the endpoint claims. The parent proof and its stated retained logical calibration are essential dependencies; the exact coefficient checks certify finite algebra and binding, not Con(ZFC).

## 8. Attribution

Incoming `conzfc_graph_digits_2026-10-24`, pinned at ProveIt `e0c98c629bf10d30b695884f6b1d2ab361bdf513`, supplies the four-pool low-digit idea and its application to the older semantic cap. Round17 supplies the aligned K=x self-sized radix, square factorial/product fusion, strict quotient ranges, canonical lift, semantic anchor, and parent literal graph. The new result is their composition with a simple uniform radix margin, weighted mixing of adjacent denominator levels, absorption of the exact output bound, and the smaller literal equations. The contractor and independently written checker are inherited from the credited package100 code and have been read in full before execution here.
