# The fixed-residue free-coordinate equation

## Theorem and interpretation

Let F be the literal integer polynomial in `integer10.json`. It has ten unrestricted integer variables, exact total degree1,576,864 and a481-operation division-free circuit. Ordinary mathematics formalizable in ZFC proves

    [F has no zero in Z^10]  iff  Con(ZFC).

Here Con(ZFC) means the nonexistence of a finite syntactic refutation in the fixed source calculus. The proof uses the identified native compiler/refutation theorem and arithmetic bridge; it is not a new end-to-end Lean/Rocq certificate. No consistency assumption or global minimality claim is made.

The complete typeset proof is `section.tex`, together with the source derivation in `../../packing/section.tex`. This file records the same final variant, not the earlier CRT or source-dependent parity prototypes.

## Literal source prefix

The ten supplied integers are t,g0,c0,k0,l,w,x,y,z,m. Put

    b=6t+4, g=bg0, k=b(3k0+2), kappa=2134940, B=2^kappa b^2,
    ell=sum_i B^wi, word=ell+g,
    Gcode=D2(B)word^2+D1(B)word+D0(B), AT=sum_j B^qj,
    N0=B^117, N=B^1991,
    mask=N0-1-(b-1)ell,
    Jcode=2Gcode+AT, Sc=g+N0 Jcode,
    Tc=mask+N0(B-2)AT-2,
    X=N(Sc+Tc+1)-Sc-1,
    Y=2^34159017 b B^2114, cap=b B^116.

The31 weights wi,22 targets qj, and three fixed polynomials D0,D1,D2 are specified in `data/code.json` and `data/kernels.json`. These are finite literal data, not quantified variables or unspecified choices. Every kernel coefficient is a fixed polynomial in the four included actual native ports, and all derived circuit leaves are also separately materialized in `fixed/`.

The shared-tap source identities, positive-gap bijections and carry proof establish the source/refutation equivalence. Their exact polynomial extraction is independently replayed. The required source interface is:

- On every signed assignment, b is even and nonzero, b=1 modulo3, X is odd and X=0 modulo3, and b divides X+1 and Y.
- If b is a positive square and0<g<2cap, then X>3b and Y>256, and the calibrated binomial divisibility with binary base decodes a positive common source zero.
- Every positive source zero has encodings with arbitrarily large b=4^s. The constructive arithmetic bridge supplies the canonical Lucas values and congruences described below.

None of the source polynomials depends on c0. The coherent source is gapN86, not the incompatible gapNq85 layout. The entire original31 four-port tuple is retained.

## Literal finalizer

Define polynomial registers

    L=lY, U=2LX, V=4gwY, W=bw,
    halfA=(LX)(V+1), A=2halfA, B1=2X+1, C=6c0-1,
    Phalf=(LX)UV, P=2Phalf, K=X+1+k(P-2),
    S=2A-5, T=3WC-2(W^2-1), Q=(Phalf^2-1)K^2+1,
    Delta=8cap^3 gK^2-g^2[32(C-KL)^2cap^3+g^2K^2],
    xi=zx, D=(A^2-4)C^2+4, E=C^2Dxi,
    F=4(A^2-4)E^2+1,
    G=2(A+2)(A-2)^2E^2-1,
    Omega=16E, H=C+F(B1-C+Omega y), I=(G^2-1)H^2+1,
    rho=T+Sy, Sigma=xi S^5,
    Theta=(rho^3-rho S^2-S^3)(rho^2+23S^2),
    r=bQ, delta=9Delta-3, a0=r+delta(rz)^2, a1=DFI,
    Z=Sigma m-Theta.

The equation is

    (Z^2-Sigma^2(a0+a1))^2-4Sigma^4 a0 a1=0.       (E)

All powers are fixed nonnegative integers. The names halfA and Phalf denote the explicitly displayed polynomial registers; there is no division in the equation. In the circuit G is shared as `(halfA-1)(F-1)-1`, an identical polynomial.

## Strengthened Lucas-index lemma

Let6 divide A, B=3 modulo4,1<B<|A|/2-1, C=5 modulo6, and xi!=0. Define D,E,F,G,Omega,H,I as above with B in place of B1. If DFI is a square, then C=u_B(A), where u0=0,u1=1,u_(n+2)=A u_(n+1)-u_n.

The point is that no hypothesis(A-2)|(C-B) is required on this fixed residue slice. The proof follows.

C is odd and nonzero. Since |A|>2, the three integers D,F,I are positive. The certificate identities F=I=1 moduloD and4I=D moduloF, with F odd, make them pairwise coprime. Therefore each is a square. The Pell/Lucas classification gives integers s,mu,t with

    C=u_s(A), 4E=u_mu(A), H=u_t(2G).

Put n=|mu|. We have n>3, since |4E|>=4D>|u3(A)|. Parity gives n even and s,t odd. The standard Lucas index-separation lemma applied moduloF gives s=+t or-t modulo2n. The rank-divisibility lemma applied to C^2|u_n(A) gives C|n. The identities2G=-2 moduloOmega and H=B moduloOmega give t=B moduloOmega. As2C dividesOmega, it follows that

    s=B or-B modulo2C.                            (1)

So far only the congruence-free part of the existing certificate argument was used; oddness and nonvanishing of C are supplied directly.

For all integer A and j>=1, the recurrence proves the polynomial congruences

    u_(2j)(A)=(-1)^(j-1)jA moduloA^2,
    u_(2j+1)(A)=(-1)^j moduloA^2.                 (2)

Indeed the base cases are u2=A,u3=A^2-1, and the next two recurrence steps establish the pair at j+1. This proof works for negative A as well.

If s=+/-1, then C=+/-1 and D=A^2. Consequently A^2 divides u_n(A). Write n=2j. The first formula(2) gives A|j. Hence2|A| divides both2n andOmega=16A^2xi. Combining s=+/-t modulo2n with t=B moduloOmega would force B=+/-1 modulo2|A|, contrary to1<B<|A|/2-1. Thus |s|>=2. This argument does not assume n|u_n(A).

Lucas growth now gives |C|=u_|s|(|A|)>=|A|>B and |s|<=|C|. A nonzero multiple of2C cannot occur in(1), so s=B or s=-B. Since B=3 modulo4, the second formula(2) gives u_B(A)=-1 moduloA^2, hence modulo3. The branch s=-B would give C=+1 modulo3, contrary to C=5 modulo6. Therefore s=B and C=u_B(A), proving the lemma.

## Fully signed soundness

Take any integer zero of(E). The source and k normalization imply b|K and3|K, so Q is odd, Q=1 modulo b^2 and modulo3, and gcd(b,Q)=1. On every assignment A=0 modulo3 and C=-1 modulo3, so D=0 modulo3 and a1=0 modulo3. In contrast r=bQ=1 modulo3 and delta=0 modulo3, so a0=1 modulo3. In particular a0!=a1 without assuming any signs.

S=2A-5 is odd and nonzero. The quintic pi(v)=(v^3-v-1)(v^2+23) has no rational root, so Theta=S^5 pi(rho/S) is nonzero. If Sigma were zero, the polynomial would equal Theta^4, a contradiction. Thus xi,z,x are nonzero. Write q=Z/Sigma. The equation implies(q^2-a0-a1)^2=4a0a1. Since a0!=a1, q!=0. The rationals

    u=(q^2+a0-a1)/(2q), v=q-u

have squares a0,a1. Rational roots of monic integer square equations are integral. Thus a0,a1 are integer squares, q is integral, and Sigma|Theta. A prime-valuation comparison in the two homogeneous factors of Theta shows that S^5|Theta forces S|T.

Factor a0=r(1+delta r z^2). The two factors are coprime and nonzero, and r=1 modulo3 excludes the negative signed-square possibility. Thus both are positive squares. The same argument applied to r=bQ gives b and Q positive squares, using their coprimality and residue1 modulo3. In particular b>=4. If Delta<=0 then delta<=-3 and the bracket would be negative, impossible. Hence Delta>0. Its defining expression yields K!=0 and0<g<2cap. If l=0 then Q=1-K^2<=0, again impossible. Also f_old=2t+1 is nonzero.

The source bounds now apply: X>3b and Y>256. Since V is a multiple of4, V+1 is nonzero; hence

    |A|=2|l|XY|V+1|>=2XY>2B1+2.

We have6|A, B1=3 modulo4, C=5 modulo6 and xi!=0. The new lemma gives C=u_B1(A). Reducing its recurrence moduloA-2 then yields(A-2)|(C-B1) as a consequence. Restore the proof-only integer h=(C-B1)/(A-2). All hypotheses of the existing reverse arithmetic bridge now hold, so it gives the binary-base binomial divisibility. The fixed source decodes a positive zero, hence a finite ZFC refutation. No arbitrary auxiliary input was silently assumed positive.

## Completeness

Given a positive source zero, choose the canonical source and arithmetic witnesses. They have C=u_B1(A),6|A and B1=3 modulo4. Formula(2) gives C=-1 modulo3; C is odd. Thus c0=(C+1)/6 is an integer. The old constructive congruences still produce k0 in the imposed class.

Here r=bQ is a positive square and Delta>0. The positive integer delta=3(3Delta-1) has3-adic valuation exactly1 and is nonsquare; so is delta*r. Pell's theorem gives positive u,z satisfying u^2-delta*r*z^2=1, making a0=ru^2 square.

The modified Lucas interpolation theorem first chooses a positive xi divisible by this z, and then allows every residue class of y modulo that fixed xi while retaining a1=DFI square. Set x=xi/z. Write v0=T/S, an integer. The quintic pi is intersective, so choose y moduloxi with pi(v0+y)=0 moduloxi. Then Sigma|Theta. The integer

    m=Theta/Sigma+sqrt(a0)+sqrt(a1)

satisfies(E). This proves the reverse existence implication. Combining both directions with the source/refutation calibration and negating proves the stated ZFC-provable consistency equivalence.

## Exact degree and evidence

The source gives degX=7962,degY=4229, and a=degA=16424. Since C has degree1,

    degD=2a+2, degE=2a+6, degF=6a+12, degG=7a+12,
    degH=8a+19, degI=30a+62, dega1=38a+76,
    degSigma=5a+2.

The guard and center have strictly lower degrees than the unique dominant final summand Sigma^4 a1^2. Therefore the degree is96a+160=1,576,864. Independent nonzero diagonal leading coefficients with the actual fixed tuple certify that the upper bound is attained.

`check.py` independently replays300 complete source-plus-finalizer modular cases,1000 unconditional residue cases and3120 paired-recurrence cases, as well as literal coefficients, topology and exact degree. Separate producer-free checks in `../../free_carrier_audit/` confirm the degree and finalizer formulas. Exact symbolic source extraction is replayed in `../../packing/audit.py`. All these finite checks support transcription and degree, not the unbounded semantic theorem.

Primary arithmetic references are Sun's2021 Theorems4.12--4.13 at https://arxiv.org/html/1704.03504v7 and the modified Lucas/index/interpolation results of https://arxiv.org/html/2609.01594v1 . The compiler and original source proof dependencies are preserved under `provenance/`, with source pins and original license material. No inherited program is executed in this reproduction.
