# Independent supplement: fourteen-integer double-centered carrier

## Verdict and scope

PASS. This is a valid ordinary two-way reduction to the already-reviewed fifteen-integer equation. The literal sibling has fourteen unrestricted integer variables, exact degree 108, and 119 live binary gates: 69 multiplications, 30 additions, and 20 subtractions. The fifteen-integer review is unchanged.

No new native/compiler calibration, end-to-end proof-assistant certificate, encoded internal-ZFC derivation, consistency proof, or global-optimality result is asserted. The exact source34 coefficient tuple is unchanged. This supplement audits the new arithmetic and its integer witness maps, not the inherited compiler theorem afresh.

## 1. Exact double-centered identity

Use the sibling's notation A=2L+k, B=2(a+2)I, aa=4-k^2, bb=4(1-I^2), and t=Z/U. Independently expanding the two expressions gives the universal identity

    [t^2+2Bt+aa-bb]^2
      +4(t+A+B)[A(t^2+2Bt-bb)-aa(t+B)]
    = [(t+A+B)^2-(A^2+aa)-(B^2+bb)]^2
      -4(A^2+aa)(B^2+bb).

Multiplication by U^4 yields the historical centered expression. The current 119-gate evaluator computes the identical polynomial directly as [E0^2-4U^2(Dtau+Df)]^2-64U^4 Dtau Df. The independent checker compares the complete two formulas, including the cancellations in the shorter schedule. The two defects are exactly

    A^2+aa=4Dtau,
    B^2+bb=4Df,

where Dtau=1+XY^2(XY^2+1)k^2 and Df=1+Delta I^2. Therefore N=0 is the four-sign norm equation for the rational center t+A+B and the real radicals 2sqrt(Dtau), 2sqrt(Df). The checker verifies the complete polynomial identity, not only sampled evaluations or a claimed factorization.

## 2. CRT and all exceptional branches: monicity first

The inherited affine arithmetic establishes U!=0 and gcd(H,2q^2)=1 on every integer assignment, independently of any root extraction. At N=0 the rational number

    x=Z/U+A+B

satisfies the monic integer polynomial

    x^4-2(4Dtau+4Df)x^2+(4Dtau-4Df)^2=0.

The rational-root theorem consequently gives x in Z. Since A+B is integral, Z/U is integral too. Thus U divides Z and the same coprime CRT argument immediately gives

    v=q^2(2v0+1), v0 in Z, and H divides Klo.

In particular v cannot be zero. This order handles the v=0 exceptional branch without assuming any weak-scale bound or prior rationality of the individual radicals. It also covers a hypothetical zero signed sum, equality of radicands, or a vanishing strong ordinate before the guard is used: monic integrality needs none of those cases excluded.

This is important because the rationality of a sum of two radicals alone need not imply rationality of each when their signed sum is zero. The proof does not use that invalid inference. It obtains CRT from the monic quartic first, then uses the guard and recovered scale to exclude cancellation before extracting the roots.

## 3. Root separation from exactly the available budget bounds

The unchanged guard supplies k!=0 and |eta/k|<1/2. Put x=|X|, m=|Y|, K=|k|. After CRT, x>=64, m>=|q|^3>=4096 and K>=1. In fact the following proof works already at the weaker m>=16.

The centered interval gives |c|>K(m-1/2)>3Km/4. Also

    sqrt(Delta)>(x-1)m-3>xm/2.

Thus c is nonzero and, because |2r+1|>=1,

    f=sqrt(Df)>sqrt(Delta)c^2>(9/32)xm^3 K^2.

For ell=XY^2, |ell|=xm^2 and ell(ell+1)>=0 even when ell<0. Therefore

    tau=sqrt(Dtau)
      <=K sqrt(ell(ell+1)+1)
      <K(xm^2+1)<(9/8)Kxm^2.

Consequently f/tau>mK/4>=4, hence certainly f>2tau. This estimate assumes neither eta positivity nor a positive sign for X,Y,c,I, or the root-center B.

The exact norm gives a signed rational sum s=epsilon*tau+nu*f. Separation makes s nonzero. The elementary formula

    tau=(s^2+Dtau-Df)/(2 epsilon s)

makes tau rational and then f rational. Each has integer square, hence each is an integer. Both are positive as chosen square-root magnitudes. No square-class independence or unproved multiradical extraction lemma is needed.

## 4. Complete two-way integer witness maps

Fourteen to fifteen: retain every shared coordinate except n, introduce f15=f, and use the CRT integers

    g=Klo/H, v0=(v-q^2)/(2q^2).

Choose n15=tau-L-g-v0. Then Z15/U=tau-L, so the fifteen-variable first row vanishes. Its strong row vanishes since f15^2=Df, and its Q,V,auxiliary row and budget are exactly the fourteen-variable values. This is a literal zero of the reviewed fifteen-variable equation. Only after that restoration is its signed main-root/compiler theorem invoked.

Fifteen to fourteen: from any fifteen-variable zero take tau=|Z15/U+L| and f=|f15|, which are positive integer Pell roots by the already-reviewed theorem. Keep the shared arithmetic and guard coordinates, and choose

    n14=2tau+2f-A-B-g-v0.

Then Z14/U+A+B=2tau+2f, so one factor of the exact norm vanishes. All f-dependent expressions depend only on f15^2 and therefore agree. The auxiliary and budget rows vanish unchanged. The signs of I and B do not matter, since n14 is unrestricted and the displayed expression is integral.

These maps work for every zero in either direction. They require no canonical witness restriction, no positivity of the new carrier coordinate, no unproved quotient divisibility, and no extra quantified register.

## 5. Exact degree and cost

Independent exact expansion of the generic norm, with the actual front-end degree bounds, gives

    deg(N)=54, deg(auxiliary)=42, deg(guard)=16.

Write root-center leading parts as A*=2L*, B*=2a*I*. Since Z*=U*n, the unique degree-54 contribution is

    N*=8U*^3 A*^2 B* Z*
       =64U*^4 L*^2 a*I*n.

Therefore N^2 is the only degree-108 contribution. Selecting the h term in k*=R*+hX*Y* gives the exact coefficient

    [j^56 w^18 v^22 h^4 r^2 c^4 n^2] P14
      =2^130 3^74 beta^56>0.

The exponents sum to 108. Thus the degree is attained on the actual coefficient slice, not merely on generic coefficients. All fourteen input leaves and all 119 binary operations are live, and all scalar multiplications and squares are charged.

## 6. Reproducible finite evidence

The separate independent checker does not import the sibling builder. It verifies 37 register-cut identities, the full generic norm and both defects, monicity of the normalized quartic, the generic weighted degree upper bound, front-end leading components, the selected coefficient, all graph references and live inputs, and the six authentic coefficient hashes. With the pinned baseline available it also compares complete source coefficient bytes directly.

Sixteen intentional live-node mutations are rejected, including both root centers, the direct norm arguments and inner expression, N, Df, the auxiliary row, guard and finalizer. Normal and optimized-Python run receipts are included. These finite results certify algebra, transcription and accounting, not the inherited unbounded source theorem or Con(ZFC).
