# Repair of the critical-weight bound in the high-path estimate

Supporting derivation, 2 October 2026. The ternary specialization is independently reviewed in the DFA transfer audit. This note does not modify the cited paper.

Let q=k-1>=1 and U(i,j)=q^2(i-j+k)/(qi+j), on active up-step destinations j>=1. Then U decreases with j and

U(i,j)<=U(i,1)=q[1+(q^2-1)/(qi+1)]<=q[1+(q-1/q)/i].

Thus any path of length t has weight at most C_q t^(q-1/q) q^(number of up steps). At a point (kx,ky), its up/down counts are qx+y and x-y. Consequently

d_(kx,ky)<=C_q (kx)^(q-1/q) q^(qx+y) binom(kx,x-y).

This replaces the false printed pointwise claim U<=q in the arXiv-v1 proof of Lemma14. The extra factor is polynomial and is harmless for y>x^(3/4): the centered binomial deviation has exp(-c y^2/x), while the published endpoint lower bound costs only exp(O(x^(1/3))) and powers of x. Summing over y and then x>I gives a tail tending to zero uniformly in terminal size, once the bridge comparison below is established.

## Elementary bridge comparison

Let p(r,s;T) count weighted continuations to (T,0), and set u_r(s)=p(r,s;T)/(s+1) for nonnegative heights of the correct phase. Its backward recurrence has coefficients

A_r(s)=U(r+1,s+1)(s+2)/(s+1),
B_r(s)=(s-q+1)_+/(s+1).

Their sum V_r(s) is nonincreasing in s. If s<q-1, B=0 and both factors in A decrease. If s>=q-1, exact algebra gives

V_r(s)=k-qk [(s-q+1)/(s+1)] [(s+2)/(q(r+1)+s+1)].

Both bracketed factors are nonnegative and increasing; the second derivative has sign q(r+1)-1>=0. At s=q-1 the formulas join at k. Hence the row sum decreases everywhere.

Adjacent same-phase starts s and s+k have next supports {s-q,s+1} and {s+1,s+k+1}, omitting a negative-height point with zero coefficient. If the next normalized continuation sequence is nonincreasing, every left-support value is at least the common middle value and every right-support value is at most it. Nonnegative coefficients and V_r(s)>=V_r(s+k) preserve the inequality. The terminal normalized sequence is1 at0 and0 elsewhere, hence nonincreasing. Reverse induction proves p(r,s)/(s+1) decreases on each physical phase.

In particular p(kx,ky;T)<=(ky+1)p(kx,0;T). Dividing bridge mass at (kx,ky) by endpoint count and comparing through (kx,0) gives

P_T(path visits (kx,ky)) <=(ky+1)d_(kx,ky)/d_(kx,0).

The repaired binomial bound above therefore supplies the same uniform high-path tail claimed in Lemma14, with an additional harmless polynomial factor. All constants may depend on fixed k. No amplitude conclusion is inferred from this lemma alone.
