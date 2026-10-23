# A completed-square Jones equation in nine natural or positive unknowns

## The result and its scope

Put L=5^32. The file `generated/nine_sharp_natural.json` is an integer-coefficient polynomial F in exactly nine nonnegative integer unknowns. Its total degree is exactly

    92324 L+296 = 2149585634469985961914062796.

The supplied division-free circuit has 1505 binary additions, subtractions and multiplications. The positive-integer version `generated/nine_sharp_positive.json` has the same degree and 1500 operations. Every other named quantity is a circuit register, not an existential unknown. Fixed coefficient construction is not charged as variable arithmetic, but all coefficient recipes are bounded and explicit below.

Using the inherited ordinary compiler, literal K215 calibration and parameterized Jones arithmetic theorems, ordinary mathematics formalizable in ZFC proves

    (there is no x in N^9 with F(x)=0) iff Con(ZFC).

Equivalently the positive version has no strictly positive zero iff Con(ZFC). This is an equivalence, not a proof of Con(ZFC), a new kernel-checked endpoint, a variable-minimum theorem or a globally optimal circuit. N means {0,1,2,...}. No assertion is made for nine unrestricted integers.

This synthesis takes the 31-witness quartic and its exact compact943 binding from source 30, the unconditional sign lemmas and signed finalizer from source 28, and the shared-power/homogeneous/Horner coefficient evaluator from source 27. Its new completed-square majorants improve source 28's degree; additional exact circuit rewrites reduce the cost. Sources are pinned to VladimirReshetnikov/ProveIt commit 8c6eec9d19ef80538c8e61ff6e0180040583446a. See SOURCE_PINS.json and the source notices. Earlier Jones, DPRM, native-window/Pell and literal-machine contributions retain their attribution.

## 1. One fixed compiler tuple, not four parameters

Use exactly the four unsigned little-endian integers in `../coefficients/COMPACT_COEFFICIENT_BINDING.json`:

    beta = B_native-1, with B_native=2^(5^10);
    K0 = K = DC+B_native DR;
    MC = the compact943 data mask;
    MF = MF_source = MF_native+B_native-1.

The complete finite tile/machine, positional layout, coefficient generator, correctness proofs, materializations and checksums are in `../coefficients/`. In particular MF is already shifted; do not shift it again. This is the source 30/source 19 compact tuple, not source 27's smaller mixed-radix tuple. No port is mixed between constructions. Its ordered port bit lengths are

    (9765625,13201251,9765625,9765626).

The complete compiler-correctness contract, including positive completion and its quotient convention, is an imported ordinary mathematical dependency. A hash or modular check alone cannot establish that contract.

## 2. The explicit normalized quartic in 31 witnesses

The ordered strictly positive parent coordinates are

    J,F,alpha,zp,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma,
    N,E,P,c,a,X,D,C2,L,F2,V,g,I,Baux,Delta.

Only in this subsection set q=beta J+1, k=eta+zeta, H=4a+3 and Cw=q-F-alpha. The 22 quadratic residuals are:

1. L-q^2+1.
2. N-q(L+1).
3. X-wq.
4. a-E-sN.
5. E-X(a-E).
6. c-k(a-E)-eta.
7. P-E(c-eta)-k.
8. tau^2-P(P-k)-1.
9. D-X-ac-gamma H.
10. Delta-a^2-H.
11. C2-c^2.
12. D^2-Delta C2-1.
13. k-jc+V-1-hE.
14. jc-V-(q-F)(N-q)+Cw L-(MC+q MF)J.
15. (K0+w)Cw+q-F-zp(q-1)-1.
16. F2-f^2.
17. V-of+c.
18. g-y^2+V^2.
19. I-i C2.
20. Baux-I^2.
21. Baux-Delta(F2-1).
22. y^2-Baux g-1.

These expressions, expanded as sparse coefficient arrays, are source 30's literal `arithmetic/quartic31.json`; its SHA256 is 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287.

For completeness, source 30 removes the old 32nd register Gp from the previous quartic. Its definition was Gp=(q-1)(q-F)+alpha=q(q-F)-Cw. On N=q(L+1),

    L Gp=(q-F)(N-q)-Cw L.

Thus replacing the old Gp-definition and packing equations by row 14 is exact in both directions. The recovered Gp is positive: row 15 gives (K0+w)Cw+(q-F)=1+zp(q-1)>=q. If Cw<=0, its left side is at most q-F<q, impossible. Thus Cw>0, q-F=Cw+alpha>0 and Gp>0. This proves the positive-domain elimination without altering the source transport quotient.

Let r_1,...,r_22 be the displayed residuals and define

    P31(x,n_1,...,n_31)=sum_j r_j(n_1+1,...,n_31+1)^2.

The dummy x does not occur. The degree is exactly four, since the coefficient of n_tau^4 is one. At n=0, row 5 equals one, so P31(x,0)>=1 regardless of the fixed ports. By the inherited positive quartic/native compiler and literal K215 calibration, P31(1,.) has a natural zero iff ZFC has a finite syntactic refutation.

## 3. Every Jones constant has a finite recipe

Set nu=31, L=5^(nu+1). For alpha=(alpha_0,...,alpha_31) with |alpha|<=4, let p_alpha be the coefficient of x^alpha_0 n_1^alpha_1 ... n_31^alpha_31 in P31. Define

    c_alpha=(4-|alpha|)! product_j(alpha_j!) p_alpha;
    expo(alpha)=sum_j alpha_j 5^j.

Unlisted coefficients are zero. There are exactly 402 nonzero symbolic coefficient records in `source/30-quartic31/nine/nu31/COMPACT_CONSTANTS.json`; each is a small explicit polynomial in the four fixed ports. The verifier regenerates these records from the literal parent. The expanded parent has 675 terms with ports retained symbolically.

For c_alpha=sum_t a_t product_j port_j^e_tj, put

    H_alpha=sum_t |a_t| 2^(sum_j e_tj bitlength(port_j)).

The actual coefficient has |c_alpha|<=H_alpha. The supplied sparse powers-of-two index certificate checks the exact integer inequality

    H_alpha+1 < 2^45933757

for every record. Consequently the following bounded definitions specify an admissible Jones index:

    z=2^45933757;
    u_index=sum_(j=1)^31 (2z)^(5^j);
    y=sum_(|alpha|<=4) (z+c_alpha)(2z)^(L-expo(alpha));
    e(T)=sum_(|alpha|<=4) (z+c_alpha)T^(L-expo(alpha)).

All 58,905 eligible alpha occur in the baseline sum, even when c_alpha=0. All digits satisfy 1<z+c_alpha<2z, and the exponent positions are distinct. Hence y>0, b=y+1+epsilon>=2, and all index requirements of Jones1982.Index31 P31 are satisfied. The parameterized theorem Jones1982.Nine.wset_iff_nine applies with x=1>0 and nu=31. The public convenience theorem's separate nu=58 normalization is not used. The native radix exponent 5^10 is unrelated to the number of quartic witnesses and cannot justify nu=9.

The index z is also materialized in `generated/z_index.bin`; y and the weighted coefficients remain finite recipes. No search, run of K215 or unspecified enumeration index occurs in any definition. u_index is part of the proof interface, not a final polynomial leaf.

## 4. The nine-coordinate polynomial

From here all notation is local to the Jones construction. The unknowns are

    epsilon,g0,h0,s0,w0,phi,i0,j0,n in N.

Set g=g0+1,h=h0+1,s=s0+1,w=w0+1,i=i0+1,j=j0+1 and define

    b=y+1+epsilon, B=b^5, q=B^L;
    ell=sum_(a=1)^31 B^(5^a), lambda=sum_(a=0)^(4L-1) B^a;
    e=e(B), theta=B-2z, N=q^16, Gcap=32b B^(5^31).

Let

    Rleft=g+e q^3+ell q^5
          +[2(e-z lambda)(1+B+g)^4+lambda B+lambda B q^4]q^7;
    Rright=q^3-b ell+ell+theta lambda q^3+(B-2)q^8;
    R=Rleft(N^2-N)+Rright(N^2-1).

The implementation factors powers inside these brackets by distributivity only. Continue with the unchanged Jones ratio expressions:

    U=N^2 w, Y=N^2 s, M=R Y, P=2M^2 U;
    K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw;
    C=B1+W1+phi, J=4A-5, Q=3W1 C-2(W1^2-1);
    D=(A^2-1)C^2+1, E=i J D C^2, F=(A^2-1)E^2+1;
    G=A+F(CD+1-A), H=B1+jC, I=(G^2-1)H^2+1;
    a0=(P^2-1)K^2+1, a1=DFI;
    u=JF, v=QF+J(H-C);
    m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2.

Set

    sigma=Y(U+1), r=W1+phi, s1=r+1;
    MD=A C+sigma s1^2+1;
    MF=A E+1;
    TCH=C H+r^2;
    MI=F(D TCH+2H^2+A^2)-A^2+1;
    V0=P K+1, V1=MD MF MI+1;
    Mdiv=Q^2+(H-C)^2+1;
    Omega=u(2m-1);
    Theta=u(n+Mdiv)+v-Omega(2Mdiv+V0 V1).

Finally,

    F9=(Theta^2-Omega^2(a0+V0^2 a1))^2
       -4 Omega^4 V0^2 a0 a1.

The requested equation is F9=0. All exponents are fixed nonnegative integers. There are no radicals, divisions, variable exponents or additional quantified registers in this equation.

## 5. Unconditional sign and majorant lemmas

Every assertion in this section holds on every natural assignment of the eight outer coordinates, before any square, divisibility or margin condition is imposed.

Modulo q, the packed expression satisfies R=(b-1)ell mod q: q divides N and every term in Rright other than (1-b)ell is divisible by q. Since b>=2 and the exponent support of ell lies in 0,...,L-1,

    0<(b-1)ell <=(B-1)ell <=q-1<q.

Thus R is a nonzero integer. As U,Y>=1, sigma>=2 and A=R sigma, we have |A|>=2. Also P=2R^2Y^2U>=2R^2>=2 and

    K=R+1+h(P-1)>=R+P>=2R^2+R>=1.

Consequently J=4A-5 is nonzero, AJ>0, D>=1, AE=i AJ D C^2>=0 and F>=1. These facts are inherited from source 28, whose proof does not assume R positive.

The new D-majorant uses C=2R+s1. It satisfies

    MD-AC=sigma s1^2+1>0;
    MD+AC=sigma(4R^2+2R s1+s1^2)+1>0.

The quadratic expression is nonnegative because

    2(4R^2+2R s1+s1^2)=(2R+s1)^2+4R^2+s1^2.

Therefore MD>=|AC|+1>=1. Since D=(AC)^2-C^2+1>0,

    D <= (AC)^2+1 <= (|AC|+1)^2 <= MD^2.

For MF, AE>=0 gives MF>=1 and

    F=(AE)^2-E^2+1 <= (AE+1)^2=MF^2.

Next H=(j+1)C-r, so

    TCH-CH=r^2>=0;
    TCH+CH=2(j+1)C^2-2rC+r^2
           =C^2+(C-r)^2+2jC^2>=0.

Hence TCH>=|CH|. Moreover G=FDC+F-A(F-1). Using F,D>=1 and the integer inequalities |H|<=H^2 and |AH|<=A^2+H^2,

    |GH| <= FD TCH+F H^2+(F-1)(A^2+H^2).

Adding |H|+1<=H^2+1 proves

    |GH|+|H|+1 <= FD TCH+2F H^2+(F-1)A^2+1=MI.

Thus MI>=1 and sqrt(|I|)<=|GH|+|H|+1<=MI. Finally, because P,K>=1,

    1<=a0=(PK)^2-K^2+1<=(PK)^2;
    sqrt(|a1|)<=MD MF MI.

Therefore V0,V1>=2 and sqrt(|a_t|)<=V_t-1 for t=0,1. The proofs include C=0,H=0 and negative R. The natural-domain R!=0 lemma is crucial; arbitrary unrestricted-integer assignments are not covered.

## 6. Signed-divisor finalizer, with both directions

We give the complete source 28 combining lemma. Let integer a0,a1,u,v,m,M,V0,V1 obey

    u!=0, M>=1, |v/u|<=M-1;
    V0,V1>=2, sqrt(|a_t|)<=V_t-1.

For n in N define Omega=u(2m-1), Theta=u(n+M)+v-Omega(2M+V0V1), and the displayed F9. Then

    exists n in N: F9=0

is equivalent to: a0,a1 are integer squares, u divides v, and m>0.

Indeed Omega!=0. Choose complex roots r_t^2=a_t. Direct multiplication gives

    F9=product_(epsilon,delta in{-1,1})
         [Theta-Omega(epsilon r0+delta V0 r1)].

A zero has a vanishing factor; absorb its signs into the roots. The rational number s=Theta/Omega equals r0+V0r1. If s!=0, the identity 2s r0=s^2+a0-V0^2a1 makes r0 and r1 rational, hence integers because their squares are integers. If s=0, then |r1|=|r0|/V0<1, and the integer |a1|<1, so a1=a0=0. This argument covers zero roots, negative candidate radicands and repeated square classes without an independence assumption.

Put Z=2M+V0V1+r0+V0r1. The bounds give Z>=2M+1>0. The vanishing factor, divided by the possibly negative u, reads

    n+M+v/u=(2m-1)Z.

Its left side is >=n+1>0, forcing m>0. Its right side is integral, forcing u|v. Conversely, if the three conditions hold, choose any integer roots and set

    n=(2m-1)Z-M-v/u.

This is an integer at least 2M+1-M-|v/u|>=2. Its corresponding factor vanishes.

In our application u=JF!=0 and

    v/u=Q/J+(H-C)/F.

Since J is a nonzero integer and F>=1,

    |v/u|<=|Q|+|H-C|<=Q^2+(H-C)^2=Mdiv-1.

Thus the lemma applies unconditionally. The divisions here occur only in the proof, not in the circuit.

## 7. The semantic chain

Eliminating the ninth natural coordinate therefore recovers precisely the unchanged four Jones ratio conditions: a0,a1 are squares; JF divides QF+J(H-C); m>0. The inherited parameterized Jones ratio_sound/ratio_complete and packing reductions identify existence of the eight outer coordinates with a zero of P31(1,.), because Sections 2–3 discharge their normalized-quartic and admissible-index hypotheses. The exact positive quartic31 elimination, the coherent compact943 native/Pell compiler and literal K215 blank-run calibration identify this with a finite ZFC refutation. Negating gives the stated ZFC-provable equivalence. Finite tests validate definitions and implementations, not this unbounded semantic assertion or consistency itself.

## 8. Exact total degree and the cancellation certificate

All fixed coefficients have degree zero. Substituting all nine inputs=t gives the following degree/leading-coefficient pairs; ordinary total-degree upper bounds agree. Write L=5^32:

    R:235L /1; sigma:320L+2 /1; r:2 /1;
    A:555L+2 /1; C:235L /2; H:235L+1 /2;
    P:950L+3 /2; K:950L+4 /2;
    D:1580L+4 /4; E:2605L+7 /64;
    F:6320L+18 /2^12; G:8135L+22 /2^15;
    I:16740L+46 /2^32;
    a0:3800L+14 /16; a1:24640L+68 /2^46;
    u:6875L+20 /2^14; m:2221L+11 /(-2^9);
    MD:790L+2 /2; MF:3160L+9 /64;
    MI:8370L+23 /2^16;
    V0:1900L+7 /4; V1:12320L+34 /2^23;
    Omega:9096L+31 /(-2^24).

The leading terms of V1^2 and a1 cancel. Here are exact polynomial telescoping identities resolving the cancellation, not a numerical leading-term guess. Put t0=sigma(r+1)^2. Then

    deltaD=MD^2-D=2AC t0+t0^2+2AC+2t0+C^2;
    deltaF=MF^2-F=2AE+E^2;
    Wminus=MI-GH=FD r^2+2FH^2+(F-1)A^2+1-FH+A(F-1)H;
    deltaI=MI^2-I=Wminus(MI+GH)+H^2-1;
    deltaV=V1^2-DFI
      =deltaD MF^2 MI^2+D deltaF MI^2+DF deltaI
       +2MD MF MI+1.

The first two terms 2AC t0 and t0^2 in deltaD have respective degrees1110L+8 and640L+12; the other terms are smaller. Thus deltaD has degree 1110L+8 and leader 4. deltaF has degree 5210L+14 and leader 2^12. Wminus has degree 7900L+22 and leader 2^14, so deltaI has degree 16270L+45 and leader 2^31.

The first three displayed deltaV summands have degrees

    24170L+72; 23530L+64; 24170L+67.

The first uniquely dominates, giving deltaV degree 24170L+72 and leader 2^46. This remains true for every specialization of the fixed ports.

Let E0=u(n+Mdiv)+v-2Omega Mdiv. Exactly,

    Theta^2-Omega^2(a0+V0^2a1)
       =E0^2-2E0 Omega V0V1
        +Omega^2 V0^2 deltaV-Omega^2a0.

The third term uniquely dominates with degree 46162L+148 and leader 2^98. The final subtracted term 4Omega^4V0^2a0a1 has degree 68624L+220, below 92324L+296. Squaring therefore gives exactly

    deg F9=92324L+296, with diagonal leader 2^196>0.

The generator emits `nine_sharp_degree_certificate.json`, an exactly equal polynomial with these telescoping substitutions. Its gate-by-gate symbolic-leading audit has no unresolved positive-degree cancellation. Modular agreement tests supplement, but do not replace, the displayed exact identities.

## 9. Circuit evaluation, coefficient aliases and domain translation

Let T=5^nu, t_j=B^(5^j), v_j=B^(T-5^j). Generate t_(j+1)=t_j^4 t_j, v_nu=1 and v_j=t_j^4 v_(j+1). Define w=(t_nu,v_0,...,v_nu). The exact exponent identity

    B^(5T-expo(alpha))=t_nu t_nu^(4-|alpha|) product_j v_j^alpha_j

gives

    e(B)=t_nu[z h4(w)+sum_alpha c_alpha t_nu^(4-|alpha|) product_j v_j^alpha_j].

Use the ascending complete-homogeneous recurrence to compute h4, and the deterministic recursive multivariate Horner order in build_nine.py to compute the correction. All 402 aliases in COEFFICIENT_ALIASES.json are either literal integers or exactly identical polynomials in the four ports. Only 78 distinct nonliteral coefficient leaves remain, besides z and y. The aliases are identities of recipes, not observed coincidences modulo primes.

For lambda use

    lambda=product_(j=0)^nu S5(t_j) (1+q)(1+q^2),
    S5(t)=1+(t^2+t)(t^2+1).

The latter saves a multiplication per nontrivial ladder entry compared with 1+t(1+t)(1+t^2). Further distributive power factoring in R and a0=(PK)^2-K^2+1 are exact. Every fixed exponent is expanded into multiplications; scalar multiplications and squarings are charged; repeated nodes are shared.

To translate to strictly positive coordinates use epsilon=epsilon_plus-1, phi=phi_plus-1,n=n_plus-1, and g0=g-1,etc. Thus b=y+epsilon_plus and g,h,s,w,i,j are directly the supplied positive coordinates. The nine-variable translation is a bijection of domains, preserves total degree, and eliminates five gates overall. It does not extend the theorem to unrestricted integers.

## 10. Reproduction and limitations

Run `python3 build_nine.py`, then `python3 verify_nine.py` from this directory or by absolute path. The latter expects the sibling coefficients folder. Standard Python 3.10+ suffices. Use integer-preserving JSON parsing; degrees/exponents exceed 2^53.

Checks include literal parent normalization and all 402 weighted recipes, exact 58,905-position baseline/correction identity, all 402 alias identities, four authentic compiler-byte hashes and bit lengths, all 402 strict index bounds, exact symbolic-leading certificate, actual-instance source 28/certificate modular comparisons, both positive shifts, signed/zero-edge majorants and signed-divisor finalizer fixtures. See generated/VALIDATION.json for the executed ledger. They neither test unbounded solvability nor prove consistency. Imported formal and ordinary mathematical dependencies are identified rather than falsely claimed to have been rebuilt in a proof-assistant kernel.

