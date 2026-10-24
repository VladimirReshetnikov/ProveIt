# Norm saturation removes one high-degree square factor

## Completed equation and scope

The literal circuit `integer10.json` defines an ordinary polynomial in ten unrestricted integer variables. Its exact degree is 1,245,324 and it has 480 live binary arithmetic operations, with fixed integer leaves free. It combines the certified H1868 packing with the same twelve actual fixed integer leaves as the round10 equation of degree1,576,864 and481 operations. The new result improves degree and removes one operation without adding variables. The unchanged H1873 source version separately has481 operations and degree1,248,364; the extra reduction here comes from certified target repositioning and an exact shared power plan. It is not a global minimality or historical priority claim.

Ordinary mathematics formalizable in ZFC proves that the new polynomial has an integer zero if and only if the fixed source calculus has a finite ZFC refutation. Negating gives the requested consistency equivalence. The native arithmetic/compiler calibration is inherited explicitly; this is not a new end-to-end Lean/Rocq certificate.

## 1. Exact change

Use the certified H1868 packing source, retaining the round10 guard, divisibility merger, and final norm. The packing change retains the same source polynomials and weights but improves the target placement; its separate full proof is in the accompanying packing/certified component. In particular the ten integers are t,g0,c0,k0,l,w,x,y,z,m, and

    b=6t+4, g=bg0, k=b(3k0+2), C=6c0-1, xi=zx,
    L=lY, U=2LX, V=4gwY, W=bw,
    A=U(V+1), B1=2X+1, S=2A-5, T=3WC-2(W²-1),
    Phalf=(LX)UV, K=X+1+k(2Phalf-2),
    Q=(Phalf²-1)K²+1,
    Delta=8cap³gK²-g²[32(C-KL)²cap³+g²K²].

The fixed polynomials X,Y,cap use the certified H1868 sparse source under `data/`, evaluated by `build.py` and independently by `independent_formula.py`. For definiteness, with kappa=2134940 and Bcode=2^kappa b², write ell=sum Bcode^wi, word=ell+g, coded=D2(Bcode)word²+D1(Bcode)word+D0(Bcode), target=sum Bcode^qj, N0=Bcode^117, N=Bcode^1986. Then

    mask=N0-1-(b-1)ell,
    Sc=g+N0(2coded+target), Tc=mask+N0(Bcode-2)target-2,
    X=N(Sc+Tc+1)-Sc-1,
    Y=2^34159017 b Bcode^2109, cap=b Bcode^116.

The literal31 weights,22 target exponents and three fixed sparse polynomials are in `data/code.json` and `data/kernels.json`; actual integer coefficient payloads are included, not unspecified MRDP parameters.

Replace only the old square used by F and G. Define

    D=(A²-4)C²+4,
    E0=C²xi, E=D E0, E2=E0 E=C⁴Dxi²,
    F=4(A²-4)E2+1,
    G=(A/2-1)(F-1)-1,
    Omega=16E,
    H=C+F(B1-C+Omega y), I=(G²-1)H²+1.

Here A/2 is the integer polynomial (LX)(V+1), not a rational operation. In the old equation F and G used E²=C⁴D²xi². We replace this by E2=C⁴Dxi² but retain Omega=16C²Dxi. E0,E,E2 need the same three multiplications as the old E and E². The auxiliary square root of D will exist only inside the proof, never as an extra variable.

Set

    rho=T+Sy, Sigma=xi S^5,
    Theta=(rho³-rho S²-S³)(rho²+23S²),
    r=bQ, a0=r+(9Delta-3)(rz)², a1=DFI,
    Z=Sigma m-Theta.

The single ordinary polynomial equation is

    (Z²-Sigma²(a0+a1))²-4Sigma⁴a0a1=0.          (N)

All exponents are fixed natural numbers and all intermediate names are polynomial abbreviations.

## 2. Generalized certificate reliability

Assume A is even, |A|>2, B is odd with1<B<|A|/2-1, C is odd with|C|>1, and xi!=0. Use D,E0,E,E2,F,G,Omega,H,I above, with B replacing B1. If DFI is square, then C=+u_B(A) or -u_B(A), where u0=0,u1=1,u_(n+2)=Au_(n+1)-u_n. On the actual residue slice 3|A, B=3 modulo4, C=-1 modulo3, the sign is positive.

Proof. D,E2,F are positive; |G|>1 and I>0. Since D divides E2, F=1,G=-1,I=1 moduloD. Also

    2G=(A-2)F-A,
    4I=D moduloF.

Because F is odd these prove pairwise coprimality of D,F,I. Their square product therefore makes each a square. Choose the proof-only positive integer d with d²=D. Pell/Lucas classification gives integer indices s,mu,t such that

    C=u_s(A), 4C²d xi=u_mu(A), H=u_t(2G).

C odd implies s odd. Since |C|>1, |s|>=3; Lucas growth gives |C|>=|A|²-1. Consequently |4C²d xi|>|u3(A)| and n=|mu|>3. This order of argument matters: the bound on C is obtained from classification, not assumed for arbitrary inputs. The evenness of u_mu implies n even, and F=(v_n(A)/2)². H and t are odd.

Reduction moduloF and the standard Lucas index-separation lemma imply s=+t or-t modulo2n. Since C² divides u_n(A), the usual rank-divisibility lemma gives C|n. Thus s=+t or-t modulo2C.

For the modified definitions,

    (F-1)/(Omega xi)=(A²-4)C²/4,
    (2G+2)/(Omega xi)=(A+2)(A-2)²C²/4,

both integers because A is even. Hence F=1 and2G=-2 moduloOmega. It follows that H=B moduloOmega and H=u_t(-2)=t moduloOmega, because t is odd. Since2C dividesOmega, s=+B or-B modulo2C. Now |s|<=|C| and B<|A|<|C|. A nonzero multiple of2C cannot equal s-B or s+B, so s=+B or-B exactly.

Finally the elementary recurrence congruence u_(2j+1)(A)=(-1)^j moduloA² gives u_B(A)=-1 modulo3 when3|A and B=3 modulo4. Therefore C=-1 modulo3 selects C=u_B(A).

The only external interfaces in this paragraph are the classical Pell classification, index separation and rank-divisibility statements recorded as Lemmas2.1,2.2 and Corollary2.1 in Sun's modified-certificate paper. No exceptional-index exclusion from the old equation is reused.

## 3. Full residue-class interpolation survives saturation

Let A>2 be even, B>0 odd, C=u_B(A), and d=v_B(A)>0, so D=d². For every positive N there is a positive xi divisible by N such that every residue class moduloxi contains a y with DFI square for the new definitions.

Choose a positive matrix period n modulo4NC²d for M_A=[[A,-1],[1,0]]. Then4NC²d dividesu_n(A). Set

    xi=u_n(A)/(4C²d), r0=v_n(A)/2.

These are positive integers, N dividesxi, n is even, r0 is odd, and F=r0². In the modified construction

    Omega=16C²d²xi=4d u_n(A).

Cayley-Hamilton supplies the same period lambda=4nr0 moduloF as in the usual interpolation argument. Put q=lambda/gcd(lambda,Omega). We claim gcd(q,xi)=1. For p|xi, F=1 moduloxi implies p does not divide r0. The Lucas valuation inequality gives nu_p(u_n(A))>=nu_p(n), including p=2 because A is even. Therefore

    nu_p(lambda)=nu_p(4n)<=nu_p(4u_n(A))<=nu_p(Omega).

Every prime power oflambda supported onxi is absorbed byOmega, proving the claim.

Given a desired y class c moduloxi, choose arbitrarily large positive L with q|L and L=c moduloxi. Let j=B+Omega L, an odd positive integer, and H0=u_j(2G). Since lambda dividesOmega L and2G=-A moduloF, we have H0=C moduloF. Also2G=-2 moduloOmega gives H0=B moduloOmega. The identities F=1 moduloOmega show gcd(F,Omega)=1. Thus

    y=(H0-C-(B-C)F)/(Omega F)

is an integer and H=H0. Working moduloOmega xi, the two displayed quotient identities in section2 give H0=B+Omega L and C+(B-C)F=B. After cancellation, Fy=L moduloxi, and F=1 moduloxi gives y=c moduloxi. Finally Pell identities make I a square. D,F,I are all squares, as required.

This proves a genuinely modified interpolation theorem. Merely multiplying the old xi by d would not have justified arbitrary residue classes modulo the new xi; the argument above establishes that missing property directly.

## 4. Soundness on all signed assignments

The unchanged source and normalizations give b=Q=1 modulo3, gcd(b,Q)=1, 3|A and3|K. Consequently a0=1 modulo3 while a1=0 modulo3, even before any sign has been determined. In particular a0!=a1.

S is odd and nonzero. The intersective quintic pi(v)=(v³-v-1)(v²+23) has no rational root, so Theta!=0. At a zero of(N), Sigma cannot be zero. The usual two-square norm identity and a0!=a1 show that a0,a1 are integer squares and Sigma dividesTheta: write q=Z/Sigma, derive q!=0, and note that [(q²+a0-a1)/(2q)]²=a0 and the complementary rational square equalsa1; rational squares of integers have integral roots. Then q is integral. The prime valuation argument for the homogeneous monic quintic yields S|T. Also xi,z,x are nonzero.

Factor a0=r[1+(9Delta-3)rz²]. Its two factors are coprime. The residue r=1 modulo3 excludes negative signed squares, so r is a positive square. The same argument for r=bQ yields b,Q positive squares. If Delta<=0, the second factor would be negative; thus Delta>0. The unchanged guard estimates give K!=0 and0<g<2cap. If l=0, Q=1-K²<=0, impossible. The source bounds now give X>3b and Y>256, hence |L|=|l|Y>=Y and |A|>=2XY>2B1+2.

One new observation eliminates all exceptional Lucas coordinates before using section2. From Delta>0 and g>=1,

    4(C-KL)²<K².

Therefore

    |C| >= |KL|-|C-KL| > |K|(|L|-1/2) >= Y-1/2 >1.

This replaces the old standalone exceptional-index argument, whose stronger D-factor would no longer be available. We can now apply section2: C is odd,3|A, B1=3 modulo4, C=-1 modulo3 and xi!=0. Thus C=u_B1(A). Its recurrence implies A-2 dividesC-B1. Restore the proof-only quotient h=(C-B1)/(A-2); the existing reverse binomial arithmetic bridge then applies unchanged. The fixed source decodes a finite refutation.

## 5. Completeness

A refutation supplies the same canonical source and arithmetic witnesses as before, with C=u_B1(A), A>2 even, C=5 modulo6, r=bQ a positive square, Delta>0 and S|T. Take c0=(C+1)/6. The integer delta=9Delta-3 has3-adic valuation exactly1. Therefore delta*r is positive nonsquare. Pell's theorem supplies positive z and u with u²-delta*r*z²=1, making a0=ru² square.

Apply section3 with N=z. It supplies positive xi divisible byz and full interpolation ofy moduloxi. Set x=xi/z. Since T/S is an integer and pi is intersective, choose a residue class fory making pi(T/S+y)=0 moduloxi. Interpolation realizes this class while keepinga1 square. Thus Sigma dividesTheta. The integer

    m=Theta/Sigma+sqrt(a0)+sqrt(a1)

satisfies(N). This proves existential equivalence, not a bijection between all old and new witness tuples.

## 6. Exact degree

Write a=degA=16384. The H1868 source has degX=7942,degY=4219,degcap=233. The new degrees are

    degD=2a+2, degE0=4, degE=2a+6, degE2=2a+10,
    degF=4a+10, degG=5a+10, degOmega=2a+6,
    degH=6a+17, degI=22a+54, dega1=28a+66,
    degSigma=5a+2.

The guard has degree294619 and the center degree81925, both below their competing leading terms. The unique dominant final expression is Sigma^4 a1². Hence

    deg(N)=4(5a+2)+2(28a+66)=76a+140=1245324.

The actual fixed coefficients give nonzero leading coefficients modulo independent primes, checked without importing the producer. They certify attainment rather than just a syntactic degree upper bound. The fixed coefficient payloads are byte-identical to round10. Source calibration, positivity, index recovery and interpolation are mathematical proofs; finite tests are evidence of exact transcription, not substitutes for these universal arguments.

## 7. Shared fixed-power plan

`OPTIMIZED_POWER_PLAN.json` lists every multiplication identity B^a=B^u B^v used by the prefix. Each has positive u,v<a and u+v=a. The builder validates these identities and the exact requested exponent set. The literal topological circuit independently replays the source polynomial, so no search optimality assumption enters correctness. The deterministic bounded search is optional; the exact78-step power plan is retained as data. With common-subexpression reuse across the whole graph it gives480 total binary operations. No claim of optimality of this addition plan is made.
