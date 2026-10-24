# A split scalar carrier lowers the eleven-integer degree to 416

## Status and relationship to the selected primary family

This is one additional proved degree/cost tradeoff, not a replacement of the frozen degree-464 primary. It keeps eleven unrestricted integer variables and the same six actual fixed coefficients. Its new idea is to recover the cubic Y scale through a second, coprime component of the scalar carrier instead of substituting that scale into every arithmetic register. Only the component requiring exact divisibility is raised to the fifth power; the main-Pell projection component retains the previously proved powered-divisibility reduction.

The centered equation has exact degree 416 at 125 live binary operations. Its uncentered companion has exact degree 456 at 124 operations. Their literal schedules are supplied by the separate `../norm_weak/` package. The complete ordinary calibration boundary, fixed-tuple payloads, and source proofs are those in PROOF.md and SOURCE_PINS.json. No new formal kernel certificate or minimum claim is made.

## 1. Complete fixed polynomial

All eleven variables j,C,z,h,r,v,w,T,c,n,s range over Z. The fixed coefficients beta,K0,MC,MF,cone_A,cone_B are the exact six payloads in coefficients/BINDING.json, including shifted MF. Define

    J=6j+1, q=beta*J+1, W=12w+4,
    X=qW, Y=qv, E0=XY,
    a=E0+Y, H=4a+3, Delta=a^2+H,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q*MF)J,
    k=R+1+hE0, eta=c-Yk,
    Derr=(cone_A*F-q)^2+(cone_B*C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2*eta^2,
    D=3Budget-4, L=XY^2*k, Dt=1+L(L+k),
    Dg=1+D*Dt*s^2, Pg=Dt*Dg,
    I=rc^2, Df=1+Delta*I^2,
    Q=Delta^2*I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1, Da=delta*Cy,
    K=X(3c-2X)+2,
    M=2q^2, Dcar=HM,
    zc=Dcar*T+M*K+H(v-q^2),
    Ac=(zc^2+3Dcar^2)(zc^3-19Dcar^3),
    S=srH M^5, Z=S(n+QV)-Ac,
    u=9S^2*Df, b=S^2*Da, e=81S^2*Pg.

The final polynomial is exactly the same ordinary three-root norm

    P=[(Z^2-u-b-e)^2-4(ub+ue+be)]^2-64ubeZ^2.             (1)

The direct companion uses Z=Sn-Ac. Symbols are polynomial abbreviations, not extra variables. The literal graph may reuse S=sr*Dcar*M^4 and the identity e=S^2*Dt*[(243Budget-324)*Dt*s^2+81]. These are identical polynomials, not new semantic assumptions.

## 2. The revised bootstrap: restore the scale before excluding c=0

The old argument cannot simply be quoted before recovering the scale: the new Y=qv may initially be zero. We explicitly revise the order.

As before q is even, q=2 modulo 3, |q|>=beta-1, W is nonzero, X=2 modulo 3, and |X|>=4|q|. H=4a+3 is odd and nonzero for every integer a. If v=0, a=0 and Delta=3. If v!=0, then

    |a|=|(X+1)qv| >= (|X|-1)|q|,

which is much larger than 4. Hence Delta=(a+2)^2-1>1 in either case. Dt=1+ell(ell+1)k^2>=1 for integer ell=XY^2. Q cannot equal 1, so delta is always nonzero.

M=2q^2 and Dcar=HM are nonzero. The same zero-free rational quintic pi(x)=(x^2+3)(x^3-19) gives

    Ac=Dcar^5*pi(zc/Dcar)!=0.

If S=0, the three norm radicands vanish and (1) equals Ac^8. Thus every zero has s!=0 and r!=0, but c may still be zero at this point.

Df and Da are strictly positive. When c=0, I=Q=0 and Da=1. When c!=0, r!=0 implies I!=0, |I|>=c^2, and Df>|c|+1; the same integer-distance argument using V=Df(c-R+4IT)-c gives V!=0, Cy>0, and Da>0. Therefore if Dg<0 it is the only imaginary radical in a vanishing conjugate factor, a contradiction. Dg>=0 follows. As before Budget<=0 would give Dg<=-3; thus Budget>0. The parity of q and both cone coefficients gives Budget=0 modulo 4, so Budget>=4 and Dg>0.

Modulo 3, X=-1 still gives a=H=Delta=0, while ell=XY^2 is 0 or -1. Therefore Dt=Df=Da=1 modulo 3, regardless of v. Prime-three squareclass separation applies to the positive normalized radicals

    3sqrt(Df), sqrt(Da), 9sqrt(Pg).

Their squared orders are 2,0,4+v3(Pg). Consequently they are all integers. Coprimality gcd(Dt,Dg)=1 splits Pg into Dt=tau^2 and Dg=g^2.

Crucially, the integer factor identity already gives

    S | Ac                                                  (2)

without adjacent-Pell descent and without c!=0. The integral norm uses sqrt(Da) directly; no quotient y=ytilde/delta is needed for this divisibility. This is the point that licenses the new order of proof.

## 3. The two coprime projections in the one carrier

We have H=3 modulo q and q=2 modulo 3, so gcd(H,q)=1. H is odd, hence

    gcd(H,M)=1.                                            (3)

Since M^5 divides S, (2) gives M^5|Ac. For a prime p with p^e exactly dividing M, suppose b0=v_p(zc)<e. Expand

    Ac=zc^5+3Dcar^2 zc^3-19Dcar^3 zc^2-57Dcar^5.

Dcar is divisible by M. The first term then has valuation 5b0 and each other term has strictly larger valuation, including when p divides 3,19, or 57. That is incompatible with divisibility by p^(5e). Thus M|zc. Reducing its definition modulo M and using (3) gives

    M | v-q^2.

Put v_old=(v-q^2)/(2q^2) in Z. Then

    v=q^2(2v_old+1), Y=(2v_old+1)q^3.                       (4)

The original nonzero cubic odd-multiplier scale is now restored exactly.

The other component of (2) is H|Ac. Reducing modulo H yields

    H | (MK)^5.

By (3), this implies H|K^5. Only this weaker main-projection congruence is claimed. The odd-H identity 2Kquad=HcX-K and the huge-base argument in PROOF.md Section 5 then recover the exact main projection once the pre-projection ranks are available.

## 4. Completing soundness in the correct order

Budget>0 supplies k!=0 and |c/k-Y|<1/2. Once (4) is known, |Y|>=|q|^3 and Y!=0. Therefore c=0 would give |Y|<1/2, impossible. Now c!=0, I!=0, Q>1, and adjacent-Pell descent is licensed: for the extracted integer ytilde with ytilde^2=Da, y=ytilde/delta is rational and satisfies

    QV^2-(Q-1)y^2=1.

The descent in PROOF.md Section 3 gives y in Z. All hypotheses of the original signed folding and centered pre-projection rank proof are now present, with v_old in place of the original cubic-scale coordinate. In particular c^2|I, the two auxiliary residues, the unchanged first norm, the common-sign packing bounds, and the centered strip hold exactly.

Consequently R=2r0+1 with r0>=24, the same signed main-Pell classification holds, and |H|>|X|(|X|-3)^r0. Together with H|K^5 and the authentic |X|>=2^64, the powered projection has the same strict exponent margin 436 and restores sign(c)X=2^R. The late centered orientation and half-binomial argument then regenerate an actual old signed Q41 witness and hence a finite syntactic ZFC refutation under the retained ordinary calibration.

The order is S!=0, radical realness and Budget positivity, integer-root extraction, carrier divisibility, exact cubic scale, c!=0 and adjacent descent, signed ranks, powered main projection, late orientation, source calibration. In particular no large-Y, c!=0, or Q>1 claim is used before its proof.

## 5. Completeness and fixed-witness interpolation

Start with a canonical native outer witness and its original coordinate v_old. Define the new variable

    v=q^2(2v_old+1).

All numerical values of the old front-end registers Y,a,H,Delta,F,R,k,Budget,Dt are then unchanged. Choose the positivity Pell pair s,g for D*Dt as in PROOF.md Section 7. Choose one fixed strong pair I,f with 4s c^2|I, and set r=I/c^2. Supported-modulus interpolation, proved in PROOF.md Section 6, allows every T residue modulo sr with this same strong pair.

The canonical main projection gives H|K; put kappa=K/H. Also (v-q^2)/M=v_old. The new carrier has the exact factorization

    zc=HM(T+kappa+v_old),
    Ac=(HM)^5*pi(T+kappa+v_old).

Choose an intersective root for pi(T+kappa+v_old) modulo sr, then interpolate T in that residue, keeping I,f,r fixed. It follows that

    Ac/S=H^4*pi(T+kappa+v_old)/(sr) in Z.

Finally choose

    n=Ac/S+3f+delta*y+9tau*g-QV

for the centered equation, omitting -QV for the direct one. A conjugate factor vanishes. The witness order is the same as the primary proof; the new coordinate v is fixed with the native outer data, before any Pell or residue choices.

Thus the new equations have an integer zero exactly when the same native source has a finite syntactic refutation. Their universal nonvanishing is ZFC-provably equivalent to Con(ZFC), under exactly the same retained ordinary calibration as the primary equation.

## 6. Exact degrees and attained coefficients

The total degrees of the changed prefix are

    Y:2, a:4, Delta:8, k:5, Dt:22, Budget:16, Dg:40, Pg:62,
    I:3, Df:14, Q:22, V:19, Cy:60, Da:82,
    M:2, Dcar:6, S:16, zc:7, Ac:35,
    u:46, b:114, e:94.

For the centered equation let B0=Sn-Ac, Lc=SQV. Their degrees are 35 and 57. The exact identity

    omega=Z^2-b=B0^2+2LcB0+S^2[Q(V^2+1)-1]

has degree at most 92. Two displayed terms have the same degree, so no unsupported unique-top assertion is made about omega. The paired/symmetric norm identity gives the inner bracket

    (omega-u-e)^2-4[ue+b(u+e)].

The term -4be has degree 208; every other term has degree at most 188. The final correction 64ubeZ^2 has degree 46+114+94+114=368, less than 416. Thus the entire highest form is 16b_top^2 e_top^2, and its nonzero coefficient below proves exact degree 416.

Write

    q0=6beta*j, X0=12wq0, Y0=q0v, a0=X0Y0,
    F0=12wC-q0z, R0=-q0^3F0, k0=R0+h a0.

The tie in k's leading form is essential: R0 is not to be discarded. Directly,

    S0=128sr a0 q0^10,
    b_top=2^14*s^2*r^10*c^16*a0^14*q0^26*F0^2,
    e_top=-2^16*3^5*s^4*r^2*a0^6*q0^22*Y0^6*k0^6.

Therefore

    P_top=2^64*3^10*s^12*r^24*c^32
                   *a0^40*q0^96*Y0^12*k0^12*F0^4.

Select the h^12 term in k0^12 and the C^4 term in F0^4. This gives

    [j^212 w^56 v^64 h^12 s^12 r^24 c^32 C^4]P
       =2^388*3^278*beta^212 > 0.

The exponent sum is 416. No other term of k0^12 contributes h^12, so the tie cannot cancel this coefficient. Its positivity uses only the authentic beta. Selecting instead the R0^12 term and then the C^16 term gives the separately actual-DAG-verified endpoint

    [j^224 w^56 v^52 C^16 s^12 r^24 c^32]P
       =2^400*3^290*beta^224 > 0.

Its exponent sum is also 416.

For the direct equation Z has degree 35, and b of degree 114 is the unique largest squared argument. The norm has top form b_top^4, of degree 456. An attained coefficient is

    [j^216 w^64 v^56 s^8 r^40 c^64 C^8]P_direct
       =2^400*3^280*beta^216 > 0.

The literal norm package independently verifies the cancellation identity and the C^16 centered and C^8 direct coefficient certificates against the exported division-free schedules. The finite tests do not replace the signed soundness or completeness argument above.
