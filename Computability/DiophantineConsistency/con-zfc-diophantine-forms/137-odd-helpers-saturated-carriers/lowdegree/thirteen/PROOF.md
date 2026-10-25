# Parity-separated three-root norm: thirteen integers, degree 156

## Result and inherited boundary

The fixed polynomial `equation.json` has thirteen unrestricted integer variables, exact total degree 156, and 127 live binary arithmetic operations. Explicit maps on every zero prove equivalence of zero existence with the pinned fifteen-integer free-scale degree-44 source. The unchanged source34 ordinary compiler/calibration theorem therefore gives the same ZFC-provable equivalence between absence of integer zeros and syntactic Con(ZFC).

This is an ordinary reduction, not a proof of consistency, a new encoded object-language ZFC derivation, an end-to-end proof-assistant certificate, or a global optimum claim. The immediate source is `../source/FREE_SCALE15_PROOF.md` and `../source/free_scale15_equation.json`; all source pins and all six complete coefficients are unchanged. The full inherited source closure remains in the containing archive.

The new device eliminates both the strong Pell root f and the triangular positivity coordinate p3. The radicands replacing p3 and the first Pell root are odd, so fixed weights 1,2,4 give distinct least 2-adic coefficient valuations in every common square class. This replaces a large archimedean separation scale. It does not assert that three pairwise distinct radicands alone have no cancelling signed sum.

## 1. Complete literal equation

All thirteen unknowns are unrestricted integers:

    j,C,z,h,r,v,w,T,c,n,y,p1,p2.

The six fixed integers beta,K0,MC,MF,cone_A,cone_B are the identical complete source payloads, with MF already shifted. Define polynomial abbreviations, not additional witnesses:

    J=6j+1, qm=beta J, q=qm+1, W=12w+4,
    X=qW, Y=v, F=(K0+W)C-z qm,
    R=(q(q-F)-C)(q^2-1)+(MC+q MF)J,
    E=XY, a=E+Y, H=4a+3, Delta=a^2+H,
    k=R+1+hE, eta=c-Yk, L=E(Yk),
    I=(2r+1)c^2, Ds=Delta I^2, Fs=1+Ds,
    Q=Delta Ds, V=Fs(cT-R)-c,
    q3=q^3, M=2q3, U=MH, Klo=X(2X-3c)-2,
    Z=Un+M Klo+H(Y-q3),
    Derr=(cone_A F-q)^2+(cone_B C-q)^2,
    budget=(Yk)^2(q^2-Derr)-q^2[4(Y eta)^2+(k q3)^2],
    G=4(budget-p1^2-p2^2)-3,
    carrier=(Z+Uk)^2+4U(LZ-U),
    auxiliary=V^2-(Q-1)y(2V+y)-1,
    Dt=1+L(L+k), U2=U^2,
    ga=U2 G, db=4U2 Dt, fc=16U2 Fs, gc=ga+fc,
    inner=(carrier-gc)^2-4(ga fc+db gc),
    N=inner^2-64 ga db fc(carrier+db).

The single defining equation is

    P=(N+1)(auxiliary+1)-1=0.

All powers are fixed natural powers; the fully inlined DAG has only integer leaves, variable leaves, and binary addition, subtraction, multiplication. There are no radical or division operations in the literal polynomial.

## 2. The norm identity and exact conjunction

For proof only, put

    b=2L+k, Rnum=Z+Ub, rho=Rnum/U.

The denominator U is unconditionally nonzero, as proved in Section 3. The old carrier identity gives Rnum^2=carrier+db. Define the symmetric degree-eight norm

    F8(S;g,d,f)=[(S-g-d-f)^2-4(gd+gf+df)]^2-64gdf S.

Its signed-root factorization is

    F8(x^2;g,d,f)=product_(epsilon in {+1,-1}^3)
        (x-epsilon1 sqrt(g)-epsilon2 sqrt(d)-epsilon3 sqrt(f)).

This is a polynomial identity, proved by multiplying the eight factors, so it applies over the complex numbers and does not assume positive radicands. Substituting S=carrier+db, g=ga, d=db, f=fc gives exactly the literal N above. Equivalently,

    N/U^8=product_epsilon
        (rho-epsilon1 sqrt(G)-2epsilon2 sqrt(Dt)-4epsilon3 sqrt(Fs)).  (1)

The polynomial N is a square modulo 4, because it is inner^2 minus a multiple of 64. Thus N cannot equal -2. If (N+1)(auxiliary+1)=1, both integer factors are units; N+1 cannot be -1 and hence both are +1. Therefore, on every unrestricted integer assignment,

    P=0 iff N=auxiliary=0.

No nonnegativity premise on either residual is used. This is a tailored application of the standard integer unit-product trick; the universally valid product_i(3R_i+1)=1 encoding would also work, at additional scalar-multiplication cost.

## 3. Unconditional parameter signs and parity

The authentic beta=2^1064921-1 is odd and greater than 1, so q is even and nonzero. Also H=4a+3 is odd and nonzero. Hence U=2q^3H is nonzero on every integer assignment. Since W=12w+4 has |W|>=4,

    X is even, |X|>=4|q|>=8.

The integer a=(X+1)Y is either zero or satisfies |a|>=7. Consequently

    Delta=(a+2)^2-1 >= 3,     Fs=1+Delta I^2 >=1.

Thus the strong radicand is positive without having used a guard, Pell equation, or scale conclusion. Put D=XY^2. It is even, and D(D+1)>=0; therefore

    Dt=1+D(D+1)k^2 >=1, and Dt is odd.

The literal guard radicand satisfies G=1 modulo 4, so G is odd and nonzero.

If N=0 and G<0, every signed factor in (1) has a nonzero imaginary part from its sole imaginary radical sqrt(G), while the Dt and Fs radicals and rho are real. No factor can vanish. Hence a zero necessarily has G>0. Both G and Dt are therefore positive odd integers, while Fs is positive but is not assumed odd.

## 4. Exact square-class extraction using weights 1,2,4

Every positive integer B can be written uniquely as B=u^2 d with u a positive integer and d a positive squarefree integer. Write

    G=u1^2 d1, Dt=u2^2 d2, Fs=u3^2 d3.

Because G and Dt are odd, d1,d2,u1,u2 are odd. From N=0 one signed factor in (1) vanishes, giving

    rho=epsilon1 u1 sqrt(d1)+2epsilon2 u2 sqrt(d2)
         +4epsilon3 u3 sqrt(d3) in Q.                       (2)

Distinct squarefree radicals, including sqrt(1)=1, are linearly independent over Q. One proof is to adjoin the square roots of the finitely many primes involved and use the sign-change automorphisms: averaging against the character of one squarefree product selects only that coefficient.

Group the terms of (2) by equal squarefree d. For each d>1, its total coefficient must therefore be zero. This cannot happen:

- A group containing the G term has one odd coefficient, while all its other coefficients are even. Its signed total is odd.
- A group not containing G but containing Dt has coefficient 2u2 with exact 2-adic valuation 1; its only possible other term is divisible by 4. Its signed total is 2 modulo 4.
- A group containing neither of those terms consists only of the nonzero Fs coefficient 4epsilon3 u3.

This also covers an even squarefree class: G and Dt cannot lie in it, so an Fs term in such a class stands alone and is impossible. No oddness assumption on Fs has been made.

Every appearing squarefree class must consequently be 1. Thus all three radicals are integers. Choose their signs from the vanishing factor and write

    g=epsilon1 sqrt(G), tau=epsilon2 sqrt(Dt), f=epsilon3 sqrt(Fs).

Then g is odd and

    rho=g+2tau+4f.

This is an unbounded arithmetic proof, not an inference from finite parity samples. It uses exact 2-adic coefficient valuations within each common square class, rather than comparing the magnitudes of roots or treating distinct radicands as independent.

## 5. Complete soundness map

Take any new zero. The unit-product argument gives N=auxiliary=0, and the preceding section produces integers g,tau,f with g odd. Retain all shared old coordinates, and set

    f_old=f,
    p3_old=(g-1)/2,
    n_old=n-g-4f.

These are integers. Since Z is affine in n with coefficient U,

    Z_old/U=rho-g-4f-b=2tau-b.

The old carrier identity yields carrier_old=4U^2(tau^2-Dt)=0. Also f_old^2=Fs=1+Delta I^2 gives the old strong residual zero. In the old auxiliary row, f_old^2 is exactly the new Fs, so Q,V and the auxiliary residual are identical.

Finally,

    p3_old(p3_old+1)=(g^2-1)/4=(G-1)/4,

and the definition of G gives

    budget=1+p1^2+p2^2+p3_old(p3_old+1).

Thus the old guard is zero. We have constructed a literal zero of the pinned fifteen-variable source, with no premature CRT, sign orientation, canonical-witness assumption, or new compiler calibration. Its ordinary soundness theorem supplies a finite syntactic ZFC refutation.

## 6. Complete reverse map and canonical completeness

From any zero of the pinned fifteen-variable polynomial, delete f and p3, retain every other coordinate except set

    n_new=n_old+(2p3_old+1)+4f_old.

The old strong row gives Fs=f_old^2, and the old guard gives G=(2p3_old+1)^2. The old carrier gives an integer tau with

    Z_old/U+b=2tau, tau^2=Dt.

Indeed its rational centered-root coordinate satisfies a monic integer equation, and its root square is a multiple of 4; this is also explicitly proved in the pinned source. Consequently the new rho is

    rho=(2p3_old+1)+2tau+4f_old,

so one signed factor of (1) is zero. Its auxiliary row is unchanged because Fs=f_old^2. Therefore P_new=0.

All divisions above are proof-only and have established integrality. This reverse construction applies to every source zero, in particular to the exact simultaneous canonical source34 family obtained from a finite refutation. The canonical compiler, positivity margin, and normalized strong/auxiliary existence results are inherited unchanged. No additional rank-tuning or simultaneous representation theorem is required.

## 7. Exact degree and actual coefficient metrics

The relevant degrees are carrier:22, Fs:12, Dt:18, G:18, U:6, Q:18, V:17, auxiliary:36. The scaled radicand degrees are ga:30, db:30, fc:24; inner has degree60 and N degree120. Thus P has degree at most156.

Use the source leading forms

    q0=6 beta j, X0=12q0 w, Y0=v,
    R0=q0^4 z-12q0^3 wC,
    a0=X0Y0, U0=8q0^3X0Y0,
    Fs0=4a0^2r^2c^4, Dt0=X0^2Y0^4R0^2,
    G0=-4R0^2q0^8.

The top norm form is

    N120=2^8 U0^8 R0^8 q0^16 (q0^8+4X0^2Y0^4)^2.

The subtracted product 64 ga db fc(carrier+db) has degree114 and cannot cancel it. The auxiliary top form is

    auxiliary36=2a0^2 Fs0^2 R0 y
               =32a0^6 r^4c^8 R0 y.

The unique degree156 part of P is their product. Selecting z^9 and the q0^16 term of the squared parenthesis gives

    [j^106 w^14 v^14 z^9 r^4 c^8 y] P
       = 2^171 * 3^120 * beta^106 >0.

The exponent sum is156; the other parenthesis terms have larger w and v exponents. This proves exact attained degree for the authentic fixed constants. The literal DAG has 127 live operations: 75 multiplications, 27 additions, and 25 subtractions. Every declared input and every coefficient port is live. The same six numerals occupy 615883 uncompressed bytes. This is a variable/degree/cost tradeoff, not an assertion that it dominates the fourteen-variable degree88 or fifteen-variable degree44 endpoints.

## 8. Finite verification boundary

The independent `review/audit.py` authenticates all coefficient bytes and source pins, checks each named register at exact polynomial cuts, independently multiplies the eight signed-root factors, verifies the centered norm schedule and signed lift, proves exact leading degree and the selected coefficient, checks liveness and operation counts, exhausts finite residue cases for the conjunction, runs parity diagnostics, and rejects all live-gate mutations. It passes normally and with Python optimization enabled.

These checks verify finite transcription, algebra, and metrics. The full square-class proof is Section 4, and the unbounded compiler/refutation theorem remains the named inherited ordinary dependency; finite tests are not a replacement for either.
