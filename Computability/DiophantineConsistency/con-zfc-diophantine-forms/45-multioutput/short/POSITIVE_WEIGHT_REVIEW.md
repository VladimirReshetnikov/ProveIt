# Independent mathematical review of the degree-ten separating weight

This reviews the new positive12 construction in `../positive/`, not a
replacement for its complete definition or the inherited compiler theorem.
The reviewed choice is

    u=k^4 i, M=u(u+T),
    sigma=b+M((a+2)c-ell)+v(a+2)I,
    W=b0+H(t+sigma), L=HM+1.

The inherited definitions give I=ic^2, v=cT,
D=1+((a+2)^2-1)I^2, b=c+RD. The common weak bootstrap, including both
possible unit signs, gives q>=16, X>=q, Y>=q^3, E=XY, k>E,
0<R<q^4, c=kY+eta with 0<eta<k, and a=E+Y.

## 1. Separation: verified before recovering any eliminated root

We have

    Y<k/16, a+2<9k/8, c<17kY/16,
    sqrt(D)<(a+2)I.

The last strict bound follows from I>=1 and
(a+2)^2 I^2-D=I^2-1; in the actual bootstrap I>1.
Consequently

    v sqrt(D)/(kY^2)
    < (9/8)(17/16)^3 iT k^3 Y
    < [(9/8)(17/16)^3/16] uT
    < uT/8.

Also RY^2/k^3 < q^4/(q^3 Y) <=1/q^2<=1/256, whence

    b/(kY^2)
    < 1 + [(81/64)(17/16)^4/256] u^2
    < 1+u^2/128.

As u^2>128, these strict bounds imply

    2(v sqrt(D)+b)/(kY^2)
    < uT/4+u^2/32 < M.

The inherited inequalities sqrt(A)>kY^2 and
sqrt(G)-sqrt(A)>kY^2 therefore yield exactly the two required separations.
All subsequent disk bounds, exclusion of the zero inner root, Galois
conjugation, and rational Pell saturation use these inequalities rather
than the old formula for M. Their hypotheses are preserved.

## 2. Positivity after the translated carrier: verified

Put delta=(a+2)c-ell. This is positive because

    delta=E eta+kY^2+Y eta+2c.

At a canonical solution let g=sqrt(G) and tau=sqrt(A). Then delta<g:
g>(a+1)c and ell>c imply delta-g<c-ell<0.
The old canonical carrier parameter is

    t_old=gamma+M(g+tau)+y,

with all displayed canonical quantities positive. Since
2 sqrt(D)>(a+2)I and M tau>2(v sqrt(D)+b),

    M tau > v(a+2)I+b.

Therefore t_new=t_old-sigma is strictly positive. Soundness is immediate
from the same separation plus sigma>0 after bootstrap, which makes W>0.
No unrestricted signed variable has silently been substituted for t.

## 3. Exact degree and a uniform nonzero diagonal coefficient

Use total degree in the twelve supplied variables, all fixed ports of
degree zero. Over the algebraic Laurent field of a generic diagonal scaling,
the norm has d^8 times sixteen linear root factors. Its factor degrees are

    44 eight times; 29 four times; 27,17,25,27 once each.

The first eight retain the b term; the next four retain
v((a+2)I+sqrt(D)). For the last four, the cancellations are controlled by

    sqrt(A)=ell+k/2+O(x^-9),
    sqrt(G)=(a+2)c-c/[2(a+2)]+O(x^-11),
    sqrt(D)=(a+2)I-I/[2(a+2)]+O(x^-7).

Here O bounds need not be sharp; they hold under generic scaling of each
witness by x. The corrections to the auxiliary y root are lower order still.
Since deg(d)=46, the total degree is at most

    8*46 + 8*44 + 4*29 + 27+17+25+27 = 932.

For a concrete nonzero leading coefficient set every witness equal to x.
The fixed beta is greater than 2 for every authentic tuple. The respective
leading coefficients of the factors are

    128 beta^27(beta-1), eight times;
    64 beta^17, four times;
    -4096 beta^11, 16 beta^4(beta^5+64),
    4096 beta^10, 4096 beta^11.

The leading coefficient of d is 16 beta^28. Multiplication gives the
uniform nonzero leading coefficient of the norm

    -2^152 beta^544 (beta-1)^8 (beta^5+64).

The outer factors Nk and Nt have diagonal leading coefficients -beta^4
and -2, of degrees7 and2. Thus the product has exact degree941, with
diagonal leading coefficient

    -2^153 beta^548 (beta-1)^8 (beta^5+64).

This proves degree uniformly in authentic fixed ports, not merely at a
random specialization. The authored review checker additionally evaluates
the entire emitted circuit over several finite fields and confirms that
coefficient, while independently checking the rational numerical constants
used in the separation estimates. Finite tests supplement the proof; they
do not decide whether the authentic equation has a solution.

Review scope: mathematical audit, not a Lean/Rocq kernel certificate or an
external human review. New audit material is AI-assisted and MIT-0.
