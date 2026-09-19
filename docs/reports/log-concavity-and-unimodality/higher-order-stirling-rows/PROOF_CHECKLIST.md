# Independent proof-audit checklist

This is a guide to the ordinary mathematical proof, not an additional proof system.

1. Verify that the array is diagonal-shifted: N=n+(r-1)k. A fixed n row
   does not keep the underlying set size fixed. Check the distinguished-label
   recurrence with the two alternatives: the block has size exactly r or >r.

2. Put d=r-1 and rescale subset entries by (d!)^k. Verify that the first
   recurrence weight becomes P_d(t)=t(t-1)...(t-d+1), with t=n+dk-1.
   Adjacent columns change t by d. The Turan difference rescales by (d!)^(2k).

3. In an interior comparison put w=x_(k-2), u=x_(k-1), v=x_k, z=x_(k+1).
   Inductive log-concavity gives wv<=u^2, uz<=v^2, and wz<=uv. Check the
   exact slack decomposition (3.4). All its slack multipliers are nonnegative.

4. For subsets, B=1. The pure coefficient A_d=P_d(t)^2-P_d(t-d)P_d(t+d)
   is positive by direct comparison of the positive products
   product_j ((t-j)^2-d^2) and product_j (t-j)^2.

5. Interior indices satisfy k<=t/(d+1) and t>=2(d+1).
   The centered second difference of P_d is nonnegative by convexity.
   Therefore the mixed coefficient is bounded below by its affine
   extension at k=t/(d+1), denoted L_d(t).

6. For d=0,1,2,3, use the explicit expressions in Section 4.2. For d=4,
   verify the factorization of 4A_4-L_4^2. Each factor is positive on t>=10;
   the cubic becomes 7s^3+179s^2+1354s+3720 at t=10+s.
   Complete the square. The previous entries u,v are strictly positive.

7. Check all boundaries: rows n=0,1,2 are automatic. For k=2 one input
   neighbor is zero; for k=n-1 the other is zero. No division by either
   of those zero neighbors occurs. The division used is only by uv>0.

8. For the quantitative bound, the normalization is 24^k. The surviving
   factor is (96/25)/24^2=1/150, not 96/25 in the original subset array.

9. For necessity, r=6 fails at n=4,k=2. For r>=7, compute the three entries
   in row 3, define F(r) as the squared-middle/product-neighbors ratio,
   and prove its successive ratio is <1. All r>=7 follow from the r=7
   calculation; this is not an extrapolation from finitely many orders.

10. For cycle orders r=2,3,4, B=d^2 and the mixed coefficient is M_d.
    The d=3 discriminant is 972(t-3)^2(t-1)(t+3)>0.
    Ordinary cycle strictness comes from the first slack, not from a
    strictly positive quadratic form (which is identically zero there).

11. The fifth-order cycle obstruction is an artificial geometric input,
    not a Stirling row. It disproves universal operator preservation only.
    Neither the ordinary proof nor the finite checks settle that remaining case.

12. `certificates.py` checks coefficient identities exactly; `verify.py`
    separately cross-checks array entries by generating functions. Neither
    script is a Lean/Coq/Isabelle formalization. The all-row proof is the
    algebra and induction in the manuscript.
