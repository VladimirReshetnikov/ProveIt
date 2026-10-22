# Independent audit of the twenty-seven-integer tradeoff

Verdict: **include this variant**. The mathematical proof in
`integers/INTEGER27_PROOF.md` is valid relative to the same authentic
compiler and package-14 signed-domain theorems. No change to the frozen
twelve-positive-variable or twenty-six-integer constructions is needed.

## 1. The corrected signed-h bound is sufficient

After the main norm excludes w=0, the usual weak transport bounds give
E>R+2. The unit index equation is k=R+epsilon+hE with k>0. Thus h>=0,
and only k>=R-1 follows before restoring the first norm. The proof uses
the correct consequence

    R<=k+1<2k,

since k=eta+zeta>=2. It does not assume the unjustified stronger R<k.

Together with c<k(Y+1), this gives

    c^2+R^2 < k^2[(Y+1)^2+4] <=8k^2Y^2.

Because X>=16, A=1+L(L+k)>k^2 X^2 Y^4 has more than enough slack to give
`A>16(c^2+R^2)+1` (already Y>=1 would suffice for this estimate).

## 2. The strengthened domination and zero-t branch

For M=D+v^2 and Sgeom=Dv^2+b^2,

    M^2>=4Dv^2, M^2>=D^2,
    b^2<=2D^2(c^2+R^2).

Consequently

    4Sgeom <= M^2[1+8(c^2+R^2)] < A M^2.

Since d=Q-1>=Q/2, the strict conclusion is

    d A M^2 > 2Q Sgeom=2(e+1).

Thus C=d(t^2+M^2A)-e>e+2>0, even for t=0 and T=0. At t=0 the
resultant becomes `(C^2-D B^2)^2`. The inequality

    |B|sqrt(D)<=Q(Dv^2+b^2)=e+1<C

excludes its vanishing. Therefore t is nonzero before any division by t.

## 3. The zero-T branch is handled without dividing by B

If T=0, then B=v=0 and the resultant yields

    C^2=4d^2 t^2 M^2 A.

Here d,t,M are already nonzero. Thus tau=C/(2dtM) is rational with
integral square A, and hence is integral. The integer y=t-M tau satisfies
`dy^2=e=Qb^2-1` by direct expansion. No rational Pell saturation claim or
division by B is used in this branch.

The weak bootstrap gives Delta>R and c>2, and the nonzero odd i gives

    Q-b=(Delta-R)D-Delta-c
       >=1+Delta(i^2 c^4-1)-c>1.

Hence 1<b<Q. The equation `Qb^2-(Q-1)y^2=1` then implies |y|>=b+1,
contradicting `b^2-1=(Q-1)(y^2-b^2)`. Therefore T and B are nonzero.

## 4. Root reconstruction and completeness

All denominators in

    f=-U/(2CB), tau=(C+Bf)/(2dtM), y=t-M tau

are now nonzero. The resultant first gives rational f with f^2=D, hence
integral f. The identity `(C+Bf)^2=4d^2 t^2 M^2 A` gives integral tau;
then y is integral and `dy^2=e-Bf=Q(vf-b)^2-1`. These are the exact
normalized source equations, including the affine expression for V.

The source theorem required is the seven-positive-port theorem with odd
i and square w, not the positive-only source. It explicitly allows every
remaining supplied and recovered coordinate to be signed. Conversely its
canonical odd-i/square-w witnesses extend by `t=M tau+y`. Thus no new
completeness condition has been added.

The twenty-seven-integer count is `7*3+6`, with six free coordinates
h,T,gamma,t,r,u and seven independent positive surjections.

## 5. Independent exact-degree calculation

Give the seven positive ports and w degree two, and i,h,T,gamma,t degree
one. Then

    deg(A,Q,D,v,b,M)=(44,90,66,11,74,66),
    deg(e)=238, deg(dM^2 A)=266,
    deg(C,U,Res)=(266,532,1064).

The leaders are successively dM^2A, C^2, and U^2; each competing term
has strictly smaller degree. The outer factor degrees are 35,13,4.
Therefore the exact final degree is **1116**.

For Q0=beta J and k0=eta+zeta, direct independent multiplication gives
the final weighted leader

    -8 h gamma i^24 k0^57 w^43 s^100 Q0^343
      * [w(Q0-F-alpha)-zQ0].

Selecting the last bracket term and substituting i=2r+1, w=u^2 and the
seven positivity maps gives the exhibited degree-1116 monomial coefficient

    +2^27 beta^344,

which is nonzero uniformly for beta>0. Thus the degree proof does not
depend on numerical specialization or a generic noncancellation claim.

## Evidence boundary

The independent audit accepts the mathematical construction, not a claim
of formal-assistant certification or a global optimum. The coherent
four-coefficient backend, including the shifted MF convention, must remain
bound exactly as declared. Fresh circuit integrity/formula checks are
recorded separately in `INTEGER27_INDEPENDENT_CHECKS.json`.
