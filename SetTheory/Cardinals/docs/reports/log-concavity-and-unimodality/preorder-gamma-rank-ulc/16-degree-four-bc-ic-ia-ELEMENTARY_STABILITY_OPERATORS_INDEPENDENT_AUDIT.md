# Independent audit: elementary stability operations

Approved as an ordinary proof simplification for a future revision. The delivered role-cover package is unchanged.

For f=abA+aB+bC+D, differentiating f(t,t) and evaluating at t=z/2 gives zA+B+C exactly. This proves the physical merge using diagonalization, differentiation and positive scaling, with no missing factor of two.

The polynomial g(t,w)=t f(t,−1/t,w)=Bt²+(D−A)t−C is jointly stable: both substituted arguments are upper-half-plane whenever t is, and the nonzero factor t clears the only possible denominator. Differentiation followed by real specialization at t=0 yields D−A, stable or zero. All untouched variables remain free. This proves the stated Asano-type contraction, including its minus sign.

Applying the contraction in fresh variables x,y to f(a+x,b+y,w) gives f−∂a∂b f. The translation arguments remain upper-half-plane and multiaffinity gives the exact coefficient identity. This validates single-edge gluing without the general symbol theorem.

For the rank-two quadratic, the change to the average and difference of s1,s2 shows that F(s1,s2)=f((s1+s2)/2)−(s1−s2)²/4 retains exactly one positive quadratic-form direction. Its coefficients are nonnegative and its value is positive at every positive real vector. The already verified orthogonality argument therefore proves stability directly.

Writing α=L_P/√2 and β=L_Q/√2, the first contraction gives constant coefficient B_PB_Q−αβ and s2t2 coefficient αβ−1. The second gives B_PB_Q−2αβ+1=B_PB_Q−L_PL_Q+1. Its constant coefficient1 excludes a zero final output; a zero intermediate output would also force the final output to vanish, so the inclusive-zero closure statements are sufficient.

The standard stability closure operations and real specialization by Hurwitz were source-checked in the earlier balanced audit. This simplification removes only the general operator-classification dependency from these three operations. It does not remove the all-real multiaffine Rayleigh criterion used for the incomplete-core identities, and makes no novelty claim.
