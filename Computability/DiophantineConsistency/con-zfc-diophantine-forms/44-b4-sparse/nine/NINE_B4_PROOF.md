# A fixed equation in nine natural or positive unknowns

## 1. Result, binding, and scope

The supplied division-free circuit `generated/nine_b4_natural.json` has exactly nine nonnegative integer unknowns, exact total degree 23,321,536,264 = 38,176t+8,744 for t=610,895, and 1,383 binary arithmetic operations (488 additions, 23 subtractions, 872 multiplications). Its positive-integer translate `generated/nine_b4_positive.json` has the same degree and 1,378 operations (482 additions, 24 subtractions, 872 multiplications). All named registers are abbreviations, not quantified variables. No variable exponent, radical, division, or unspecified coefficient occurs.

With the inherited literal compiler and Jones ratio theorems, ordinary mathematics formalizable in ZFC proves that the absence of a natural zero of the first polynomial, or of a positive zero of the second, is equivalent to Con(ZFC). This does not prove consistency and is not a new end-to-end kernel-checked theorem. No unrestricted-integer nine-variable assertion is made.

The fixed parent is the literal 31-witness quartic with SHA256 1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287. The exact four ports are the **121-by-8801, 943-tile tuple** supplied in `../sun/sources/data/coefficients_binding.json`, not the older 5^10-padding tuple. Port mapping is beta=beta, K0=K, MC=MC, MF=MF_source. Their bit lengths are (1,064,921, 1,070,004, 1,064,921, 1,064,922), and all four authenticated compressed byte payloads are included there. The MF port is already shifted; do not shift it again.

Define P0(n)=sum_j r_j(n+1)^2 from the literal 22 residuals in that parent. Its 402 weighted coefficient recipes, c_alpha=(4−|alpha|)! product alpha_i! [n^alpha]P0, are in `../sun/sources/data/constants.json`, with dummy alpha_0=0 omitted from the actual code. The fifth parent residual is one at the all-one assignment, so P0(0)>0. The verified bound is |c_alpha|+1<z=2^4269855. The finite constants for the present equation are these 402 recipes, aliases thereof, and a=2^4269877. In particular a>max(2z·32^4,2048z,8). The fixed scale a is used in B=a b^4; it is not an unknown.

## 2. The sparse two-carry front end

The 31 positive weights w_i are the list in `../root_checks/bose_chowla_31_optimized.json`, with t=max w_i=610895. All 52,360 four-multiset sums from {0,w_1,...,w_31} are distinct. Consequently all sums alpha·w with |alpha|≤4 are distinct. Set L=4t, mcode=8t+1, Ecode=9t+2.

The nine natural coordinates are epsilon,g0,h0,s0,w0,phi,i0,j0,n. Put g=g0+1, h=h0+1, s=s0+1, w=w0+1, i=i0+1, j=j0+1. Define

    b=2+epsilon, B=a b^4, ell=sum_i B^w_i, q0=B^(t+1),
    Dc(B)=sum_alpha c_alpha B^(L−alpha·w),
    Mc=q0−1−(b−1)ell,
    Jc=2(1+g)^4 Dc(B)+B sum_(k=0)^(mcode−1) B^k,
    Sc=g+q0 Jc,
    Tc=Mc+q0(B−2)B^L,
    N=2B^Ecode,
    R=Sc(N²−N)+(Tc+1)(N²−1), Gcap=32bB^t.

The full fixed-polynomial coding proof is in `../signed_audit/FIXED_POLYNOMIAL_CARRY_PROOF.md`. Its original b≥a, B=b^5 choice can be replaced by b≥2, B=a b^4. Here are the two bounds needed for this substitution. On 1≤g<4bB^t, the integer inequality 1+g≤4bB^t and |Dc(B)|<2zB^L give

    |2(1+g)^4 Dc(B)|<1024z b^4 B^(8t)<B^(8t+1)/2.

For a decoded vector n_i<b, each coefficient of (1+sum n_i X^w_i)^4 Dc(X) has magnitude at most z(1+sum n_i)^4<z·32^4 b^4<B/2. Both strict inequalities follow from the displayed lower bound on a. Also B>4b and B−1>z for all b≥2; when b is a power of two, so is B=a b^4. These are all the radix hypotheses used in the mask, mixed-radix, carry, and ratio arguments. No exponent-five property is used. Briefly, the margin below gives 1≤g<4bB^t. In this range Sc,Tc lie in [0,N). Jones's ratio theorem forces b to be a power of two and N² to divide binomial(2R,R). The central-binomial carry identity splits this into the two independent block conditions. The first forces g=sum n_i B^w_i with 0≤n_i<b. The second tests the digit at exponent L of (1+sum n_i X^w_i)^4 Dc(X), which is exactly 24P0(n), by the B4 property. The added B/2 digit background is legitimate because a>2z·32^4 bounds every coefficient in magnitude by B/2. Thus the two carries are equivalent to P0(n)=0.

Conversely, a zero of P0 is nonzero because P0(0)>0. Choose a sufficiently large power-of-two b≥2, code its witnesses as g, and obtain 0<g<bB^t, hence 32g<Gcap. The same two-carry identity and Jones's ratio completeness theorem provide the eight outer witnesses. The base 2+epsilon permits every integer b≥2, including these powers of two. No unproved restriction to a sparse base sequence is used.

## 3. Unconditional positivity, stronger than the old front end

Every assertion here holds on **every** natural assignment, before imposing any Diophantine condition. The leading digit of Dc is c_0=24P0(0)≥1 at exponent L. Every other exponent is lower, and every other coefficient has absolute value <z. Since B−1>z,

    Dc(B) ≥ B^L−z(1+B+...+B^(L−1)) > 0.

Therefore Jc,Sc>0. The digits of Mc are B−b at occupied positions w_i and B−1 elsewhere below t+1, so Mc≥0. Thus Tc≥0, N≥2, and

    R≥N²−1≥N≥b≥2.

This unconditional R>0 is what permits dropping the old negative-R corrections. It follows from the fixed parent's positive constant coefficient; it is not asserted for arbitrary signed source polynomials.

## 4. Ratio registers and the new majorant

Retain the Jones ratio definitions, with their local notation:

    U=N²w, Y=N²s, M=RY, P=2M²U,
    K=R+1+h(P−1), A=M(U+1), B1=2R+1, W1=bw,
    C=B1+W1+phi, J=4A−5,
    Q=3W1 C−2(W1²−1),
    D=(A²−1)C²+1, E=i J D C², F=(A²−1)E²+1,
    G=A+F(CD+1−A), H=B1+jC, I=(G²−1)H²+1,
    a0=(P²−1)K²+1, a1=64DFI,
    u=JF, v=QF+J(H−C),
    mu=K²Gcap−4(C−KY)²Gcap−8gK².

All of A,C,D,E,F,G,H,I,K,P are positive. In particular A≥2, J≥3, and D≥A², so CD+1−A>0 and G>0. Also H−C=B1+(j−1)C>0 and C>W1 imply Q>W1²+2>0. Hence u,v>0 and

    0<v/u=Q/J+(H−C)/F ≤ Q+H−C=:Mdiv.

Now put

    t0=iJC,
    S0=t0(8D²−4D−1),
    V0=PK, V1=S0GH.

The structural observation is E=t0 DC, whence

    DF=t0²D³(D−1)+D,
    S0²−64DF=t0²(8D+1)−64D.

The second identity is an exact polynomial identity, not an asymptotic approximation. Because t0²≥9 and D≥1, its right side is at least 8D+9>0. Furthermore S0>0 and I≤G²H² because H≥1. Consequently

    sqrt(a1)=8 sqrt(DFI) < S0GH = V1,
    0<a0<(PK)²=V0², because K>1.

The factor 64 creates no new square condition: for every integer x, 64x is an integer square iff x is an integer square. The main circuit therefore keeps exactly the original Jones square predicate DFI square. No extra witness is introduced by the approximation or scaling.

## 5. A positive-divisor finalizer

Define

    Omega=u(2mu−1),
    Theta=un+v−Omega(Mdiv+V0V1),
    F9=(Theta²−Omega²(a0+V0²a1))²−4Omega^4 V0² a0 a1.

This is the requested polynomial equation F9=0. The following lemma proves both directions of the finalizer, including degenerate candidate square classes.

**Lemma.** Suppose integers a0,a1,u,v,M,V0,V1 satisfy u,v>0, M≥v/u, V0,V1≥2, and sqrt(|a_i|)<V_i. For integer mu and natural n define Omega,Theta,F9 as above with M in place of Mdiv. Then there exists n with F9=0 iff a0 and a1 are integer squares, u divides v, and mu>0.

**Proof.** Omega is nonzero because 2mu−1 is odd. Choose complex roots r_i²=a_i. The exact factorization is

    F9=product_(epsilon,delta=±1) [Theta−Omega(epsilon r0+delta V0 r1)].

At a zero, absorb the vanishing factor's signs into the roots and put s=Theta/Omega=r0+V0r1, a rational number. If s≠0, the identity 2s r0=s²+a0−V0²a1 makes both roots rational, hence integers. If s=0, then |r1|=|r0|/V0<1; as |a1| is an integer this forces a1=a0=0. Thus the roots are integer in all cases, without any square-class independence assumption.

The strict bounds now imply |r_i|≤V_i−1 because the roots have been proved integer. Let Z=M+V0V1+r0+V0r1. These integer root bounds give

    Z ≥ M+V0V1−(V0−1)−V0(V1−1)=M+1>0.

The factor equation is n+v/u=(2mu−1)Z. Its left side is positive, forcing mu>0; its right side is integral, forcing u|v. Conversely, when the three conditions hold, any integer roots give

    n=(2mu−1)Z−v/u ≥ M+1−v/u ≥1.

This is a natural integer and makes the selected factor vanish. This proves the lemma.

Apply it using the unconditional positivity and bounds in Sections 3–4. Removing n recovers precisely the four original ratio conditions: a0 square, DFI square, JF divides QF+J(H−C), and mu>0. The margin forces 8g<Gcap; the inherited ratio and carry theorems then establish the semantic chain in Section 2, ending at the fully bound quartic and the literal compiler/K215 endpoint. Negation gives the stated equivalence with Con(ZFC).

## 6. Exact degree and leading cancellation

All fixed leaves have degree zero. Diagonal specialization of all nine variables to T attains the usual total-degree bounds for the decisive registers. Their degrees and scalar parts of diagonal leaders, with t=610895, are listed below. Each leader also has a positive monomial factor in the fixed a; its exact exponent is recorded in generated/natural_DEGREE_CERTIFICATE.json. No vanishing coefficient is assumed away:

    N:36t+8,2; R:108t+24,2²;
    P:432t+99,2^11; K:432t+100,2^11;
    A:252t+58,2^6; C:108t+24,2³;
    D:720t+164,2^18; E:1188t+271,2^32;
    F:2880t+658,2^76; G:3708t+846,2^97;
    H:108t+25,2³; I:7632t+1742,2^200;
    a0:1728t+398,2^44; a1:11232t+2564,2^300;
    mu:1012t+235,−2^33; u:3132t+716,2^84;
    V0:864t+199,2^22; t0:360t+83,2^11;
    S0:1800t+411,2^50; V1:5616t+1282,2^150;
    Omega:4144t+951,−2^118.

Do not subtract degree upper bounds for V1²−a1: their highest terms cancel. Use instead the exact identity

    deltaV=V1²−a1
      =[t0²(8D+1)−64D]G²H²
       +64DF(H²−1).

Its first summand uniquely dominates, with degree 9072t+2072 and leader 2^243 a^(2268t+504). Put E0=un+v−Omega Mdiv. Then

    Theta²−Omega²(a0+V0²a1)
      =E0²−2E0 Omega V0V1+Omega²V0² deltaV−Omega²a0.

The third term uniquely dominates with degree 19088t+4372 and leader 2^523 a^(4772t+1060). The final subtracted term 4Omega^4V0²a0a1 has degree 31264t+7164, strictly below twice that degree. Therefore

    deg F9=38176t+8744=23321536264,
    diagonal leading coefficient=2^1046 a^(9544t+2120).

The generated telescoping-certificate circuits are exactly equal polynomials. Their leading-term audit reports no unresolved positive-degree cancellation. Unknown coefficient-dependent low-degree heads are left unknown, not guessed; they do not enter the decisive leaders.

## 7. Positive translation, reproduction, and limits

For the positive equation replace every natural coordinate by its positive counterpart minus one. In particular b=1+epsilon_plus, C=2R+bw+phi_plus, and n=n_plus−1. The six shifted-positive registers g,h,s,w,i,j become direct variables. This is a bijection between domains and preserves total degree. It is not a map from unrestricted integers.

Run `python3 nine/build_nine_b4.py` and `python3 nine/verify_nine_b4.py` from the package root. The verifier reconstructs all 402 weighted recipes from the 22 literal parent equations, authenticates all four compiler payloads and their 402 bounds, exhaustively checks the 52,360 B4 sums, expands the new DF and norm identities exactly, compares the independent literal formula and every named register at 240 modular assignments, checks both positive translations and cancellation certificates, and runs bounded majorant/finalizer regressions. The executed ledger is `generated/VALIDATION.json`.

These finite checks audit the data and implementation; the universal proof is the argument above and the explicitly imported number-theoretic/compiler theorems. They are not a search for a zero, a proof of consistency, a proof of minimality, or an end-to-end proof-assistant rebuild. Every source is pinned in SOURCE_PINS.json; attribution is preserved in NOTICE.md.
