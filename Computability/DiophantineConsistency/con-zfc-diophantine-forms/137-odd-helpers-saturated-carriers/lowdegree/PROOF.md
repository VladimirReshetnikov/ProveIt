# Absorb a positivity square: fourteen unrestricted integers, degree 88

## Result and exact boundary

The fixed division-free polynomial `equation.json` has 14 unrestricted integer variables, exact total degree 88, and 119 live binary arithmetic operations. Its integer-zero existence is equivalent, by explicit two-way maps on every zero, to the pinned fifteen-integer free-scale degree-44 polynomial. Thus the unchanged ordinary source34 compiler/calibration theorem yields, in ordinary ZFC, equivalence between absence of integer zeros and syntactic Con(ZFC).

This is an ordinary arithmetic reduction, not a proof of consistency, an encoded object-language ZFC derivation, a new end-to-end proof-assistant certificate, or a global minimum claim. The immediate source is `source/FREE_SCALE15_PROOF.md` and `source/free_scale15_equation.json`; copied inherited proof interfaces and all six complete coefficient payloads are pinned. The full upstream source closure is retained in the containing archive. No coefficient is reselected, and MF remains already shifted.

The new ingredients are (i) absorbing one positivity square into a two-root norm carried by the existing first-root coordinate; (ii) a global radicand-separation inequality, which makes this extraction valid even when both radicands have the same square class; and (iii) a mod-4 unit-product conjunction that avoids squaring the degree-60 norm.

## 1. Complete polynomial

The fourteen unknowns, all in Z, are

    j,C,z,h,r,v,w,T,c,n,f,y,p2,p3.

The six fixed integers beta,K0,MC,MF,cone_A,cone_B are exactly the source payloads. All following names are polynomial abbreviations, not extra unknowns:

    J=6j+1, qm=beta J, q=qm+1, W=12w+4,
    X=qW, Y=v, F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-Yk, L=E(Yk),
    I=(2r+1)c^2, Q=Delta(f^2-1), V=f^2(cT-R)-c,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Z=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(k q3)^2],
    pos2=1+p2^2+p3(p3+1), G=budget-pos2,
    carrier=(Z+Uk)^2+4U(LZ-U),
    strong=f^2-Delta I^2-1,
    auxiliary=V^2-(Q-1)y(2V+y)-1,
    UG=U^2 G,
    N=(carrier-UG)^2-16U^2 UG[1+L(L+k)].

The single equation is

    P=(N+1)(strong+1)(auxiliary+1)-1=0.

All powers are fixed natural powers and the literal evaluator uses only binary integer addition, subtraction and multiplication. In particular no rational operations, radicals, or inequalities occur in the equation. The alternative expression

    N=(carrier+U^2G)^2-4U^2G[Z+U(2L+k)]^2

is an exact identity; the displayed evaluator saves one gate.

## 2. Exact unit-product conjunction

If integers A and B cannot equal -2, then

    (A+1)(B+1)(C+1)=1

holds if and only if A=B=C=0. Indeed each integer factor is a unit, hence +1 or -1. The first two factors cannot be -1, so both are +1, and the third is then +1 as well. No sign or nonnegativity assumption on C is required. The general construction product_i(3R_i+1)=1 likewise encodes R_i=0 over integers, because -1 is not 1 modulo 3. No novelty is claimed for that universal unit-product device; the tailored residue exclusions here avoid its extra scalar multiplications.

Here N is a square modulo 4 (indeed modulo 16), so N cannot equal -2. Also write A0=a+2; then Delta=A0^2-1. If A0 is odd, Delta=0 modulo 4 and

    strong=f^2-1 modulo 4 in {0,3}.

If A0 is even, Delta=-1 modulo 4 and

    strong=f^2+I^2-1 modulo 4 in {0,1,3}.

Thus strong also cannot equal -2. Applying the preceding lemma shows, on every unrestricted integer assignment,

    P=0  iff  N=strong=auxiliary=0.

As a separately valid dependency-ordered check, strong=0 makes Q=(Delta I)^2 a square, and auxiliary+1=QV^2-(Q-1)(V+y)^2 is then 0 or 1 modulo 4. Therefore auxiliary cannot equal -2 under strong=0 either. This secondary observation is not needed for the main proof.

## 3. Unconditional nonzero denominator and radicand bounds

The authentic beta=2^1064921-1 is odd and greater than 1. Thus q is an even nonzero integer: q=0 would make beta divide 1. The integer H=4a+3 is odd and nonzero, so U=2q^3H is nonzero on every assignment. Also |W|>=4, hence |X|>=4|q|>=8.

Define proof-only integers and a rational coordinate

    D=XY^2, A=4[1+D(D+1)k^2]=4[1+L(L+k)],
    b=2L+k, t=Z/U, rho=t+b.

Because D(D+1)>=0 for every integer D, A>=4. The norm identity is

    N/U^4 = (rho^2-A-G)^2-4AG.                      (1)

If N=0, then G cannot be negative: otherwise the right side of (1) is a square plus a strictly positive real number. Thus G>=0. Since pos2>=1 for all integer p2,p3, budget=G+pos2>0. The budget is nonpositive if Y=0 or k=0, so both Y and k are nonzero. Furthermore, directly from its defining polynomial,

    budget <= Y^2 k^2 q^2.

Now |D|>=8, so D(D+1)>=D^2/2. Therefore

    A >= 4+2X^2Y^4k^2
      >= 4+32q^2Y^4k^2
       > Y^2k^2q^2 >= budget > G.                 (2)

The separation A>G>=0 follows before any Pell classification, congruence projection, scale recovery, or source soundness theorem is invoked.

## 4. Exact root extraction, including shared square classes

At N=0, (1) and A>G show rho!=0: rho=0 would give (A-G)^2=0. Set, in Q,

    p=(rho^2-A+G)/(2rho), u=rho-p.

Expansion of (1) gives p^2=G and u^2=A. A rational number whose square is an integer is integral, so p and u are integers. Since A is divisible by 4, u is even. Put

    t_old=t-p=u-b in Z.

Then

    (t_old+b)^2=A,
    t_old^2+2(2L+k)t_old+k^2-4=0.                 (3)

This is the old centered first-root equation.

The argument does not suppose independent square classes. With two roots, cancellation is the only obstruction: A>G rules it out, and the explicit rational formulas above recover both roots. This distinction is essential; mere pairwise distinctness would not in general suffice for norms with more than two roots.

## 5. Complete soundness map to the fixed predecessor

Take any integer zero of the new polynomial. Section 2 gives N=strong=auxiliary=0; Sections 3-4 give integral p and t_old. Keep every retained predecessor coordinate except set

    p1_old=p, n_old=n-p.

Because Z is affine in n with coefficient U, the predecessor numerator satisfies Z_old/U=t-p=t_old. Equation (3) gives its first carrier residual zero. Its strong and auxiliary residuals are unchanged. Finally,

    budget=G+pos2=p^2+1+p2^2+p3(p3+1),

so its guard is zero as well. This is a literal zero of `source/free_scale15_equation.json`, without a preliminary CRT assumption or a canonical-witness restriction. The pinned predecessor proof now supplies the complete signed Pell/bootstrap, late scale recovery, native compiler, and refutation soundness chain.

## 6. Complete reverse map and canonical completeness

Conversely take any integer zero of the pinned fifteen-variable polynomial. Delete its p1 coordinate, retain every other coordinate except set

    n_new=n_old+p1_old.

Then G=p1_old^2 and Z_new=Z_old+U p1_old. Writing b=2L+k and carrier_old for the old carrier evaluated at Z_old, the universal identity is

    N_new=carrier_old *
      [carrier_old+4U p1_old(Z_old+Ub)+4U^2 p1_old^2].

Thus N_new=0. The strong and auxiliary residuals are unchanged, so P_new=0. This construction applies to every old zero and uses no divisions.

In particular, given a finite syntactic refutation of ZFC, apply the pinned predecessor's exact canonical source34 family and this polynomial map. The predecessor's proof already establishes the simultaneous canonical compiler, strengthened budget, and strong/auxiliary witnesses. No new canonical rank freedom, assumption about a sum of two squares, or additional number-theoretic existence assertion is required here. The two maps need not be inverse as maps of fully signed zero sets, but they establish equivalence of zero existence on the identical coefficient tuple.

## 7. Exact fixed-coefficient degree and evaluator cost

The inherited degrees remain q:1, X:2, Y:1, R:5, a:3, k:5, L:9, U:6 and Z:7. The degrees of carrier, strong, auxiliary, G and N are respectively

    22, 12, 16, 18, 60.

For an exact nonzero coefficient, put

    q0=6 beta j, X0=12q0 w, Y0=v,
    R0=q0^4 z-12q0^3wC,
    a0=X0Y0, U0=8q0^3X0Y0, L0=X0Y0^2R0.

The top form of G is -R0^2 q0^8. Hence

    N60=U0^4 R0^4 q0^8(q0^8+16X0^2Y0^4).

The top strong and auxiliary forms are

    strong12=-4a0^2 r^2 c^4,
    auxiliary16=2a0^2 f^4 R0 y.

The unique degree-88 part of P is their product with N60. Selecting z^5 and the q0^8 term in the parenthesis gives the exact coefficient

    [j^56 w^8 v^8 z^5 r^2 c^4 f^4 y] P
      = -2^87 * 3^64 * beta^56 != 0.

The exponents sum to 88. The second term in that parenthesis has w^10v^12 and cannot contribute to this monomial. Thus degree 88 is attained for the actual fixed constants, not merely for a generic coefficient specialization.

The fully live literal DAG contains 119 operations: 67 multiplications, 27 additions, and 25 subtractions. All fourteen declared variables and all six coefficient ports are live. Compared with the historical fourteen-variable degree-108/119-operation endpoint, this strictly lowers degree at unchanged variable count and evaluator cost. Compared with the immediate fifteen-variable degree-44/111-operation source, it removes one variable at a higher degree and eight extra gates; it does not dominate that different tradeoff.

## 8. Verification boundary

`review/audit.py` independently reconstructs every named register at exact polynomial cuts, authenticates every coefficient byte and copied source hash, proves the universal norm and lifting identities, verifies the actual nonzero leading coefficient, checks liveness and literal gate counts, exhaustively checks the finite mod-4 conjunction lemma, runs signed bound diagnostics, and rejects deliberate live-gate mutations. It runs normally and with Python optimization enabled.

Those finite tests verify transcription, identities, and the stated arithmetic metrics. They do not certify the unbounded inherited compiler/refutation theorem. That theorem remains the precisely identified ordinary mathematical dependency in the containing source closure.
