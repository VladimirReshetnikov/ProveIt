# Eleven unrestricted integers, a powered scalar carrier, and degree 464

## Result and scope

The selected equation has eleven unrestricted integer unknowns, the six unchanged source34 coefficient payloads, exact total degree 464, and a literal 119-operation arithmetic circuit. Its direct companion has degree 488 and 118 operations. These improve the inspected selective-fusion parent, respectively degree 688 at 126 operations and degree 728 at 122 operations. The new reduction combines selective coprime fusion with a powered-divisibility carrier and genuinely stronger supported-modulus Pell interpolation. Switching from parity to prime-three separation permits the removal of two evenness factors. It is not merely a refactoring of the old final norm.

The conclusion, composed with the precisely retained ordinary native/compiler/refutation calibration, is that ZFC proves

    Con(ZFC) iff the displayed fixed polynomial has no zero in Z^11.

This construction neither proves either side nor supplies a new end-to-end Lean or internal object-ZFC certificate. It makes no global minimum or historical-priority claim. The full literal circuit and cancellation/degree audit are supplied separately. Their finite algebra checks do not replace the unbounded proofs below.

## 1. Fixed coefficients and complete polynomial

The independent variables are exactly

    j, C, z, h, r, v, w, T, c, n, s,

all ranging over Z without any sign restrictions. The six fixed coefficients are exactly beta,K0,MC,MF,cone_A,cone_B from coefficients/BINDING.json and the six complete compressed integer payloads. They are not parameters that may depend on the unknowns. In particular

    beta=2^1064921-1, cone_A=2^1113, cone_B=2^666104.

MF is already shifted by beta, as in the calibrated source34 family. The complete printed-seed recipe and machine/tile data accompany the payloads. Coefficient bits and circuit operations are separate complexity measures.

All following names are polynomial abbreviations, not additional unknowns:

    J=6j+1, q=beta*J+1, W=12w+4,
    X=qW, Y=(2v+1)q^3, E0=XY,
    a=E0+Y, H=4a+3, Delta=a^2+H=(a+2)^2-1,
    F=(K0+W)C-z(q-1),
    R=(q(q-F)-C)(q^2-1)+(MC+q*MF)J,
    k=R+1+hE0, eta=c-Yk,
    Derr=(cone_A*F-q)^2+(cone_B*C-q)^2,
    Budget=k^2(q^2-Derr)-4q^2*eta^2,
    D=3Budget-4, L=XY^2*k, Dt=1+L(L+k),
    Dg=1+D*Dt*s^2, Pg=Dt*Dg,
    I=r*c^2, Df=1+Delta*I^2,
    Q=Delta^2*I^2, delta=Q-1,
    V=Df(c-R+4IT)-c, Cy=QV^2-1, Da=delta*Cy,
    K=X(3c-2X)+2,
    zc=HT+K, Ac=(zc^2+3H^2)(zc^3-19H^3),
    S=srH, Z=S(n+QV)-Ac,
    u=9S^2*Df, b=S^2*Da, e=81S^2*Pg.

The equation is the single ordinary integer-polynomial equation

    P = [(Z^2-u-b-e)^2-4(ub+ue+be)]^2-64ubeZ^2 = 0.       (1)

The selected literal schedule folds the factor 81 into the guard as Dg81=(243Budget-324)*Dt*s^2+81 and computes e=S^2*Dt*Dg81. This is exactly the displayed e and saves a scalar multiplication. The direct companion changes only Z to Sn-Ac. All powers and scalar multiplications are inlined into counted binary +,-,* operations in the literal graphs. There are no radicals, divisions, implicit witnesses, variable exponents, or unresolved coefficient ports in those graphs.

The standard universal identity is

    P=product over all eps in {-1,1}^3 of
        (Z-eps1*sqrt(u)-eps2*sqrt(b)-eps3*sqrt(e)).          (2)

This is an identity of ordinary polynomials, including dependent, zero, or negative radicands. It follows by successive quadratic norms in a free multiquadratic algebra. Formula (1), not (2), defines the executable polynomial.

## 2. Unconditional facts and the exact nonzero bootstrap

J is odd and nonzero. The authentic beta is odd and is 1 modulo 3. Therefore q is even, q=2 modulo 3, and |q|>=beta-1. W is nonzero and is 1 modulo 3, so |X|>=4|q| and X=2 modulo 3. Y has an odd, nonzero multiplier of q^3. In particular |X|>=64, |Y|>=4096, |a|=|(X+1)Y| is large, H is odd and nonzero, and Delta>1.

Writing ell=XY^2 gives Dt=1+ell(ell+1)k^2>=1. Df>=1. Q is either zero, when I=0, or at least Delta^2>1; hence delta never vanishes on Z^11.

Define pi(x)=(x^2+3)(x^3-19). This polynomial has no rational zero. Since

    Ac=H^5*pi(T+K/H),

we have Ac!=0 for every integer assignment. If S=0, all three scaled radicands vanish and (1) is exactly Ac^8, which is nonzero. Every zero therefore has s!=0 and r!=0. This argument deliberately does not yet assert c!=0.

Da is positive before extracting roots. If c=0, then I=Q=0 and delta=Cy=-1, so Da=1. If c!=0, then I=rc^2!=0, |I|>=c^2, Df>|c|+1, and Q>1. For integer b0=c-R+4IT, either b0=0, giving |V|=|c|>=1, or |V|>=Df-|c|>1. Thus Cy>0, delta>0, and Da>0. Together Df>0, Dt>0, and Da>0 hold in both cases.

At a zero a factor in (2) vanishes over C. If Dg<0, the Pg term is the only nonzero imaginary term. This is impossible since S!=0. Thus Dg>=0. If Budget<=0, then D<=-4 and, using Dt>=1 and s^2>=1,

    Dg=1+D*Dt*s^2<=-3,

a contradiction. Hence Budget>0. The fixed cone coefficients and q are even; consequently both terms of Derr and q^2 are divisible by 4, and Budget is divisible by 4. Thus Budget>=4, D>=8, and in fact Dg>0. This explicitly excludes a zero guard radicand.

Budget>0 gives k!=0, Derr<q^2, and |eta/k|<1/2. If c=0, eta=-Yk and

    Budget=k^2[q^2-Derr-4q^2Y^2]<=0,

contradiction. Therefore c!=0, I!=0, Q>1, and all three normalized radicands are now strictly positive.

The disk inequality Derr<q^2 implies

    0<cone_A*F/q<2, 0<cone_B*C/q<2.

Since both cone coefficients are at least 8, F,C,q-F-C have q's common nonzero sign. Put m=|Y| and k0=|k|. The centered strip supplies

    k0(m-1/2)<|c|<k0(m+1/2), sign(c)=sign(kY).             (3)

No premature positive claim about eta or k-eta has been made.

## 3. Prime-three separation and coprime splitting

Modulo 3, X=-1, so a=H=Delta=0. Since ell=XY^2 is either 0 or -1 modulo 3, ell(ell+1)=0. Hence

    Dt=Df=1, Q=0, delta=Cy=-1, Da=1 (mod 3).              (4)

Divide a vanishing factor by S. It says that a signed sum of

    3sqrt(Df), sqrt(Da), 9sqrt(Pg)

is rational. The squared 3-adic orders of these terms are respectively

    2, 0, 4+v3(Pg).

All radicands are positive integers. In a nontrivial squareclass their square roots are rational multiples of one common irrational root. If two or more terms belonged to that class, their rational coefficients would have distinct 3-adic orders and a unique least order; their signed sum could not vanish. A singleton class cannot cancel either. Linear independence of distinct squarefree radicals therefore forces all three roots to be rational, and thus integral. This argument does not require an even I or an odd guard radicand.

We obtain integers f, ytilde, gprod with

    f^2=Df, ytilde^2=Da, gprod^2=Pg.

The essential congruence Dg=1 modulo Dt gives gcd(Dt,Dg)=1. Both factors are positive, so unique prime factorization splits their square product:

    Dt=tau^2, Dg=g^2                                     (5)

for positive integers tau,g. This is exactly the selective coprime fusion, not an assertion that a general product square splits.

The rational y=ytilde/delta satisfies

    QV^2-(Q-1)y^2=1.                                    (6)

Adjacent-coefficient Pell descent makes y integral. For completeness, if y=A/B in lowest terms then B^2 divides Q-1. The transformations

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

preserve the norm and the integrality of V'; their matrix is unimodular over Z, so they preserve the least common denominator of the pair, namely B. After reflecting signs take V,y>0. When V>1, the norm yields V<y<QV/(Q-1), which makes -V<V'<V; the norm excludes V'=0. Descent reaches |V|=1, where |y|=1, so B=1.

Thus the factor equation is an integer identity and implies S|Ac. Since H divides S, reducing the carrier modulo H gives exactly

    H | K^5.                                            (7)

We do not incorrectly infer H|K from (7) alone.

## 4. Signed folding and ranks before projection

The remaining argument uses precisely the centered signed source retained in source/centered11-proof.md, Sections 5.2-5.4, and absolute folding from source/signed-quadratic-proof.md, Section 2. We state their hypotheses and explain where they were established, to avoid hiding a positivity or parity assumption.

Put B0=|a+2|, C0=|c|, I0=|I|. We have B0>=3, 0<C0<=I0, C0^2|I0, and

    f^2-(B0^2-1)I0^2=1, |f|>2I0,
    rho=Delta*I0, Q=rho^2,
    rho^2 V^2-(rho^2-1)y^2=1,
    V=-c (mod |f|), V=-R (mod C0).                       (8)

The congruences follow from the displayed definition of V and the exact identity

    V+R=Delta I^2(c-R)+4I Df T.

Classify the strong pair by f_abs=chi_B0(m0), I0=psi_B0(m0). Classify the auxiliary pair by rho|V|=chi_rho(nu), |y|=psi_rho(nu). Its index nu is odd, since chi_rho at an even index is plus or minus 1 modulo rho. The odd quotient-polynomial identity and the first congruence in (8) give psi_B0(nu)=plus or minus C0 modulo |f|. Fold nu modulo 2m0 and reflect to a p with 0<=p<=m0. Since psi_B0(p)+C0<=2I0<|f|, no wrapping is possible, and C0=psi_B0(p), p>=1. Thus the omitted main norm is genuinely recovered before projection.

The unchanged common-sign packing bound is

    |q|(|q|^2-1)<R<|q|^4-2.

The unchanged first norm, the cubic Y scale, k=R+1+hXY, and the centered strip (3) give the pre-projection first-index bounds in the retained centered proof. Its strong divisibility argument needs C0^2|I0, not an odd multiplier: writing m0=pv and D0=chi_B0(p), composition gives I0=C0*psi_D0(v), while psi_D0(v)=vD0^(v-1) modulo C0 and gcd(D0,C0)=1. Therefore C0|v and C0|m0. The auxiliary congruences then give R=plus or minus p modulo C0. The strict inherited bounds 0<R,p<C0/2 force p=R.

These steps precede any use of (7). Their conclusions are

    R=2r0+1, r0>=24,
    c=sign(c)*psi_(a+2)(R),
    |Y|>(|X|-3)^r0/2-1.                                 (9)

The last ratio estimate follows from the same absolute centered strip, so replacing the old determinant guard by Budget has not weakened its hypotheses. No sign of X,Y,a,c,I,V,H has been discarded. As in the inherited argument, (9) implies, for x=|X|,

    |H|>x(x-3)^r0.                                      (10)

Indeed |H|>=4(x-1)|Y|-3, and substitution from (9) reduces the required strict inequality to (x-2)(x-3)^r0>4x-1, valid here.

## 5. Powered divisibility restores exact projection

Put Kquad=X(X+2ac)-1 and sigma=sign(c). The universal identity is

    2Kquad=HcX-K.                                       (11)

Since H is odd, (7) implies H|Kquad^5. The signed Pell projection identity is

    2^R*Kquad=Pi (mod H),
    Pi=(sigma X-2^R)(2^R sigma X+1).                     (12)

It is the exact congruence from source/signed-quadratic-proof.md, not a statement assuming H|Kquad. Raising (12) to the fifth power gives H|Pi^5. There is no cancellation of a nonunit modulo a composite H.

The actual beta implies x>=4(beta-1)>=2^64. Each factor of Pi has absolute value smaller than 2^(R+1)x, so

    |Pi|^5<2^(10R+10)x^10=2^(20r0+20)x^10.

Meanwhile (10) and x-3>x/2 give |H|>x^(r0+1)/2^r0. For r0>=24 and x>=2^64,

    x^(r0-9)>=2^(64(r0-9))>2^(21r0+20),

because 64(r0-9)-(21r0+20)=43r0-596>=436. Hence |Pi|^5<|H|. The integer divisibility forces Pi=0. Its second factor is odd and nonzero, so sigma X=2^R.

Now define d=sigma*chi_(a+2)(R). The signed Pell projection gives H|(d-X-ac), restoring the omitted main root and exact main congruence. The centered orientation and uniform half-binomial argument in source/centered11-proof.md Sections 5.2-5.3 now yield X,c,k,Y>0 and 0<eta/k<1/4. Section 5.4 explicitly regenerates an odd strong/auxiliary pair and an actual old signed Q41 witness. This is an existential regeneration after rank and interval recovery, not a false odd normalization of the incoming r.

Every zero of (1) therefore yields a finite syntactic ZFC refutation under the unchanged named ordinary source34/compiler calibration.

## 6. Supported-modulus interpolation with a fixed strong pair

For clarity the needed stronger interpolation theorem is restated, including the argument beyond the original modulus. Its complete proof also appears in source/POWERED_SATURATION_PARENT.md, Section 5.

Let A0>1 be even, Delta=A0^2-1, R=3 modulo 4, and c=psi_A0(R)>0 with c=R modulo 4. For a prescribed positive s, the finite Pell-matrix period supplies an even positive m0 and a strong pair

    I=psi_A0(m0), f=chi_A0(m0), 4s c^2 | I.

Keep this pair fixed throughout. The inherited valuation lemma gives v_p(m0)<=v_p(I) for every p|I. The exact squared-modulus period lambda=4m0 f is a period modulo f^2; the generally insufficient 4m0 is not used. Original full-residue interpolation supplies one positive nu0=3 modulo 4 and T0 with

    V_nu0=f^2(c-R+4IT0)-c,
    V_nu=chi_rho(nu)/rho, rho=Delta I,

at positive odd nu. Set d0=lcm(lambda,4I). For p|I,

    v_p(d0)=v_p(4I),                                    (13)

because gcd(f,I)=1 and v_p(m0)<=v_p(I). For h>=0 put nu(h)=nu0+d0*h and

    T(h)=[V_nu(h)+c-f^2(c-R)]/(4I f^2).

These values are integral. The index shift preserves the required residue modulo f^2 through lambda; it preserves divisibility by 4I through nu=nu0 modulo 4I and the identity V_nu=-nu modulo 4rho^2 at nu=3 modulo 4. Since gcd(f^2,4I)=1, the product denominator divides the numerator. Each h also has integral auxiliary ordinate psi_rho(nu(h)).

For every p|I and distinct h1,h2,

    v_p(T(h1)-T(h2))=v_p(h1-h2).                        (14)

Here are the lifting details. If D0 is a positive multiple of 4, Pell addition yields

    V_(nu+D0)-V_nu
      =V_nu[chi_rho(D0)-1]
       +psi_rho(nu)(rho^2-1)*psi_rho(D0)/rho.

For p|rho and odd nu, psi_rho(nu) and rho^2-1 are p-adic units. The elementary lifting formulas are

    v_p(psi_rho(D0)/rho)=v_p(D0),
    v_p(chi_rho(D0)-1)=2(v_p(rho)+v_p(D0))   for odd p,
    v_2(chi_rho(D0)-1)=2(v_2(rho)+v_2(D0))-1.

They follow from psi_rho(4)=4rho(2rho^2-1), chi_rho(4)-1=8rho^2(rho^2-1), binomial expansion of the norm-one unit, and the doubling formula. For odd p, multiplying the index by p raises the second-coordinate valuation exactly once; multiplying by a p-adic unit preserves it. The last binomial term at p=3 and v_p(rho)=1 has valuation 3>2, so the smallest exceptional case is also strict. At p=2, odd index multiplication preserves v2(psi_rho(4)), and each doubling raises it exactly once because the even-index chi is odd. The first-coordinate formulas then follow from (chi-1)(chi+1)=(rho^2-1)psi^2; chi+1 is a p-adic unit for odd p and has 2-adic valuation 1.

Thus the two summands in the displayed addition formula have distinct valuations, and their sum has valuation v_p(D0). Substitute D0=d0*|h1-h2|, use (13), and divide by 4I f^2 to get (14). Reversing the indices covers negative increments.

For every positive modulus M whose prime divisors all divide I, (14) makes h->T(h) a well-defined injective, hence bijective map on each finite ring Z/p^eZ for p^e|M. Finite CRT chooses one h realizing any prescribed residue of T modulo M; take a nonnegative representative. The same strong pair I,f therefore allows every residue modulo every such M, even when M does not divide I. This stronger result is exactly what permits dropping s from I while retaining sr in S.

## 7. Completeness and its quantifier order

Start with a finite syntactic ZFC refutation and the canonical centered outer witness supplied by the inherited calibration. It fixes j,C,z,h,v,w,c and has

    A0=a+2>1 even, R=3 (mod 4), c=psi_A0(R)>0,
    c=R (mod 4), Dt=tau^2,
    Derr<=q^2/2, 0<eta/k<1/4,
    Budget>q^2 k^2/4>=64.

These are the canonical centered-budget estimates, not claims about arbitrary old determinant witnesses. In particular D=3Budget-4>0. By (4), Dt=1 modulo 3, so D*Dt=2 modulo 3 and is a positive nonsquare. Ordinary Pell existence supplies positive s,g with

    g^2-D*Dt*s^2=1.

This is exactly our Dg=g^2, without a forced even ordinate. The coprime product is Pg=(tau*g)^2.

Now choose the single strong pair I,f of Section 6 with 4s c^2|I, and set

    r=I/c^2, M=sr.

Every prime factor of M divides I: those of r do because r|I, and those of s do because s|I. No claim M|I is made. The canonical main projection gives H|Kquad, hence H|K by (11); put kappa=K/H in Z.

The classical intersective quintic pi(x)=(x^2+3)(x^3-19) has a root modulo every positive integer. Away from 2,3,19, either its cubic has a simple root, or irreducible-cubic Frobenius is a 3-cycle, making its discriminant -27*19^2 a square and giving a simple root of the quadratic. At 19 the quadratic root 4 is simple. At 2 the cubic root 1 is simple. At 3, x=1+3u reduces x^3=19 to u+3u^2+3u^3=2, whose derivative is 1 modulo 3. Lifting and finite CRT finish the argument.

Choose a residue a0 modulo M such that pi(a0+kappa)=0 modulo M. Supported-modulus interpolation gives T=a0 modulo M and an integer auxiliary y, while keeping I,f,r unchanged. Consequently

    Ac=H^5*pi(T+kappa),
    Ac/S=H^4*pi(T+kappa)/(sr) in Z.

Finally choose the unrestricted integer

    n=Ac/S+3f+delta*y+9tau*g-QV.

A factor in (2) vanishes. For the direct companion omit -QV. All eleven coordinates are integers; no sign restriction is imposed on n or T.

The witness order is canonical outer data, guard Pell s/g, one fixed strong pair I/f/r, one intersective residue modulo sr, T/y, then n. No strong pair changes after the residue is chosen. Both zero-existence directions are proved, giving the stated consistency interpretation under the unchanged ordinary calibration.

## 8. Exact degree: cancellation, not a syntactic estimate

All fixed coefficients have degree zero. The relevant total degrees are

    I:3, S:8, Delta:12, Df:18, Q:30, V:23,
    Cy:76, Da:106, Dt:34, Budget:24, Dg:60, Pg:94,
    Ac:35, u:34, b:122, e:110.

For the centered equation write B=Sn-Ac and Lc=SQV, so degB=35, degLc=61, and Z=B+Lc. The exact cancellation identity is

    omega=Z^2-b
      =B^2+2LcB+S^2[Q(V^2+1)-1].                       (15)

The three terms have degrees at most 70,96,92. Thus omega has exact degree 96. Rewrite the inner bracket of (1) as

    E8=(omega-u-e)^2-4[ue+b(u+e)].                       (16)

The term -4be has degree 232; all competitors have degree at most 220, including e^2, and hence it is the unique highest term. The correction 64ubeZ^2 has degree 34+122+110+122=388, below 464. Therefore

    degP=464, P_top=16*b_top^2*e_top^2.                  (17)

For the direct equation degZ=35 and b, of degree 122, is the unique largest squared argument. Its norm has exact degree 488 and top form b_top^4.

Here is a fully attained authentic coefficient for the centered equation. Put

    q0=6beta*j, W0=12w, X0=q0W0, Y0=2v*q0^3,
    a0=X0Y0, F0=12wC-6beta*jz, R0=-q0^3F0,
    k0=hX0Y0, Dt0=h^2X0^4Y0^6,
    Budget0=-4q0^2Y0^2k0^2,
    Pg0=-12s^2h^6q0^2X0^10Y0^16,
    S0=4sra0, Q0=a0^4r^2c^4,
    V0=a0^2r^2c^4q0^3F0.

Substitution in (17) gives the full highest homogeneous form

    P_top=2^452*3^322*beta^260
      *j^260*w^52*v^64*h^12*s^12*r^24*c^32
      *(12wC-6beta*jz)^4.                               (18)

Thus

    [j^260 w^56 v^64 h^12 s^12 r^24 c^32 C^4]P
      =2^460*3^326*beta^260>0.

The exponent sum is 464. The coefficient uses only the authentic positive beta; no relation among the other five fixed ports can cancel it. This proves degree after specialization to the actual tuple, not only with generic symbolic coefficients. The literal independent audit binds (15)-(18) to the exported graph and verifies their exact polynomial identities.

## 9. Source boundary and reproducibility

The local source directory preserves the complete centered, signed-folding, strong-index, calibration, and prior arithmetic proofs with their notices. COPRIME_PROJECTION_PARENT.md records the selective-fusion parent, while POWERED_SATURATION_PARENT.md records the earlier powered projection and supported-modulus isometry. Our contribution is their compatible eleven-variable composition, with the nonzero bootstrap and prime-three separation redone after decoupling I and S.

The public comparison snapshot requested for this round is ProveIt commit 45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6. The mathematical files inherited through the supplied archives retain their own original provenance pins, principally 84e16e43092614bae262ca59651cb9d77e31a255 and the coefficient recipe's earlier source commit. A comparison pin does not rewrite an inherited source's provenance. The release ledger records the exact bytes of every retained dependency.

The equation is completely fixed by its eleven variable names, literal graph, six authenticated coefficient payloads, and output node. Reproduction checks include topology and full liveness, independent mathematical-register transcription, universal norm and centering identities, authentic coefficient hashes and recipes, exact degree, signed modular replay, and rejected corruptions. These finite checks certify the arithmetic artifact. The unbounded Pell/interpolation/source arguments remain ordinary proofs as explicitly stated above.
