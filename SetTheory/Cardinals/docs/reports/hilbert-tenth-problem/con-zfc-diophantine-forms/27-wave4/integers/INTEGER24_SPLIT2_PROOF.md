# Optional lower-degree 24-integer norm

This note changes only the first-root separating weight in `INTEGER24_PROOF.md`. Its separate artifact names contain `split2`; the unchanged baseline remains available. The full baseline reverse proof has been independently reviewed. This appendix is a separate additional construction and must not be confused with that review's original scope.

Keep all baseline quantities, particularly

    Bnd=v^2+D+2b, L=1+H Bnd, S=X+ac+Hr.

Replace the coefficient H L of tau in the norm by

    H M=2H Bnd, where M=2 Bnd.

Thus the new norm is the product over the formal signs of u^2=G and tau^2=A of

    [d(S-Lu-HM tau)^2-H^2e]^2-H^4 Baux^2D.

Its product finalizer is unchanged: Nk Nt (1+N)-1. The computed H M register uses the existing H Bnd register, so the modification adds only one gate to the emitted norm evaluator: replace H^2 L^2 by (2H Bnd)^2. L^2 and H^2 are still required elsewhere.

## Soundness

All pre-reconstruction positivity, transport and unit arguments are unchanged. The polynomial parity proof also remains valid: the first-root coefficient has merely changed from one integer polynomial to another. At X=0, A=1, so tau is already rational regardless of its coefficient; the original first separation |L|sqrt(G)>|H|Bnd still reconstructs u,y,gamma and excludes X=0. T=0 treatment, saturation and all later decoding are unchanged once the second separation is proved.

After X>0, write Z=|Y|. Then X>=16, Z>=q^3>=4096 (the following bounds use only Z>=4). We have

    |a+2|/(XZ) <= 1+1/X+2/(XZ) <= 35/32,
    |c|/(kZ) < 1+1/Z <= 5/4.

Consequently sqrt(G)<(175/128)ell<(3/2)sqrt(A). Also sqrt(A)>ell=XkZ^2>=512>4. Put B=|H|Bnd>8. Then

    |L| <= B+1 < (9/8)B,
    |L|sqrt(G)+B < (27/16)B sqrt(A)+(1/4)B sqrt(A)
                    = (31/16)B sqrt(A)
                    < 2B sqrt(A)=|HM|sqrt(A).

This is exactly the Galois separation required to force tau rational. All remaining arguments of INTEGER24_PROOF apply verbatim, including the prerequisite recovery of every root before the source negative-s exclusion is used.

For completeness, replace the baseline witness r by

    r=gamma+Bnd u+M tau+y.

Then S=Lu+HM tau+Hy, so the same canonical witnesses annihilate a norm factor. No new arithmetic or parity restriction is imposed.

## Exact degree and arithmetic cost

With the same weights as the baseline, d has degree82, H degree11, Bnd degree68, and ell degree20. A and G have the same leading form ell_top^2; L_top=H_top Bnd_top and (HM)_top=2H_top Bnd_top. The four leading linear forms after choosing u and tau signs therefore have coefficients -3,-1,+1,+3 times H_top Bnd_top ell_top. Since S has lower degree20, and H^2e has degree240 while d times the squared leading form has degree280, no lower term interferes. (The H^4 Baux^2D term has degree424, below twice280.) Hence

    N_top = 3^8 d_top^8 (H_top Bnd_top ell_top)^16,

nonzero uniformly for authentic beta>0. Its exact degree is

    8*82+16*(11+68+20)=2240.

The product has exact degree2256; SOS exact degree4480. Counts, including all 47 integer-domain substitution gates, are:

- Comparison system Nk=1, Nt=1, N00=GN11: 159 gates, 24 integers, maximum residual degree2240.
- Computed-norm system Nk=1, Nt=1, N=0: 160 gates.
- Fully computed residual system rk=0, rt=0, N=0: 162 gates.
- Single product: 164 gates, degree2256.
- Sum of squares: 167 gates, degree4480.

The independent conjugate-product evaluator and signed-bound fixture sweep are included in build_integer24.py. Finite checks corroborate exact identities and inequalities, not the semantic compiler theorem.
