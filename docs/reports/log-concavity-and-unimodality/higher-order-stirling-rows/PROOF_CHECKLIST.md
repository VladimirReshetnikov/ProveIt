# Independent proof-audit checklist

This is a guide to the ordinary mathematical proof, not an additional proof system.

1. Verify that the array is diagonal-shifted: N=n+(r-1)k. A fixed n row
   does not keep the underlying set size fixed. Check the distinguished-label
   recurrence with the two alternatives: the block has size exactly r or >r.
   Do not confuse S^(r) with the r-Stirling numbers defined by distinguished
   elements in distinct blocks.

2. Put d=r-1 and rescale subset entries by (d!)^k. Verify that the first
   recurrence weight becomes P_d(t)=t(t-1)...(t-d+1), with t=n+dk-1.
   Adjacent columns change t by d. The Turan difference rescales by (d!)^(2k).

3. In an interior comparison put w=x_(k-2), u=x_(k-1), v=x_k, z=x_(k+1).
   Inductive log-concavity gives wv<=u^2, uz<=v^2, and wz<=uv (Lemma 3.1).
   Check the exact slack decomposition (3.4). All its slack multipliers are
   nonnegative.

4. For subsets, B=1. The pure coefficient A_d=P_d(t)^2-P_d(t-d)P_d(t+d)
   is positive by direct comparison of the positive products
   product_j ((t-j)^2-d^2) and product_j (t-j)^2.

5. Interior indices satisfy k<=t/(d+1) and t>=2(d+1). Check the base index
   k=1 separately: since S^(r)_(n,0)=0 and S^(r)_(n,1)=1, the normalized
   defect there is (d!)^2>0. This is what widens the strictness claim to
   n>=2, 1<=k<=n-1.

6. For d=0,1,2,3, use the explicit expressions in Section 4.2. Two routes
   bound the mixed coefficient: the general one (affine in k, nonincreasing
   because the centered second difference Delta_d of P_d is positive by
   convexity, hence H_d >= L_d(t) := H_d(t,t/(d+1))), and — at d=4 only —
   the exact identity H_4-L_4=(96/5)*beta(t)*(t-5k) with t-5k=n-k-1>=0.
   The second is the proof; the first is still needed for Theorem 7.1 and
   for the asymptotics of Section 9, so check both.

7. For d=4, verify the certificate (4.12) in whichever of its three forms
   you prefer: the single identity 25(A_4 u^2+H_4 uv+v^2) = (5v-8*alpha*u)^2
   + 96(t-5)*beta*gamma*u^2 + 480*beta*(t-5k)*uv; the two-step form, i.e. the
   factorization of 4A_4-L_4^2 plus a completed square; or the expanded
   coefficient form in Appendix A, which needs no software at all. Each
   factor is positive on t>=10; the cubic becomes 7s^3+179s^2+1354s+3720 at
   t=10+s, and beta=2(t-3/2)^2+9/2 for all real t. The previous entries u,v
   are strictly positive.

8. Check all boundaries: rows n=0,1 carry no internal test, and row n=2 has
   only k=1. For k=2 one input neighbor is zero; for k=n-1 the other is zero
   and t-5k=0, both allowed by the certificate. No division by either of
   those zero neighbors occurs. The division used is only by uv>0. Note also
   that the induction needs only ordinary log-concavity of the input row: it
   creates strictness rather than assuming it.

9. For the quantitative bound, the normalization is 24^k. The surviving
   factor is (96/25)/24^2=1/150, not 96/25 in the original subset array.
   Audit it at the smallest index: n=3, k=2, t=10 gives A_4=16752960,
   H_4=-4944 (negative, so the coefficient-sign criterion cannot apply),
   4A_4-H_4^2=42568704>0, actual defect 87318, bound 18476.

10. For necessity, r=6 fails at n=4,k=2. Check the two entries by both
    supplied derivations — block-size pattern and recurrence — since this is
    the load-bearing numeric fact. For r>=7, compute the three entries in
    row 3, define F(r) as the squared-middle/product-neighbors ratio (or
    R(r)=1/F(r)), and prove the successive ratio moves the right way. All
    r>=7 follow from the r=7 calculation; this is not an extrapolation from
    finitely many orders. Table 1 (the third row at the threshold) shows
    why row three alone is not enough.

11. For cycle orders r=2,3,4, B=d^2 and the mixed coefficient is M_d.
    The d=3 discriminant is 972(t-3)^2(t-1)(t+3)>0. Ordinary cycle
    strictness (r=1) comes from the first slack, not from a strictly
    positive quadratic form (which is identically zero there).

12. The fifth-order cycle obstruction has two witnesses: the factorization
    64A_4-M_4^2 = -9216(t-4)(t+4)(2t-9)*beta(t) < 0 for t>=10, and the exact
    numerical input at n=5, q=7350. The latter is an artificial geometric
    input, not a Stirling row. Both disprove universal operator preservation
    only. Neither the ordinary proof nor the finite checks settle that
    remaining case.

13. Scope fences: the result-to-source map in Appendix D states exactly which
    clause of which conjecture is settled, and Example 5.2 (r=5, n=3:
    discriminant 462^2-4*126126 = -291060 < 0) rules out the real-rootedness
    and total-positivity readings.

14. `certificates.py` checks coefficient identities exactly and without a
    CAS; `code/verify_certificates.py` checks the same identities under
    SymPy; `verify.py` and `code/verify_rows.py` cross-check array entries by
    generating functions and by block-size profiles respectively. None of
    these is a Lean/Coq/Isabelle formalization. The all-row proof is the
    algebra and induction in the manuscript.
