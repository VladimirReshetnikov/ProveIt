# Odd auxiliary port: a 31-integer-variable construction

Final combined instance: use the complete four-port T4 tuple in ../bridge/T4_CONSTANTS.json. Its full compiler contract and canonical rank R = 3 modulo 4 are proved in ../bridge/BRIDGE_AUDIT.md. Historical packet06/08 coefficient discussions below document the derivation or a separate fallback, not a license to mix numerical ports. The arithmetic and witness arguments are unchanged.

This is a further existence-preserving specialization of the ordinary-strong hybrid and the six-sign relaxation in `SIGNED_DOMAIN_PROOF.md`. It leaves the selected complete coefficient tuple unchanged; the main T4 adapter and historical 06 fallback both supply the canonical parity used below.

## Result and formula

Keep only these eight ports positive:

    J,F,alpha,z,s,w,eta,zeta.

Replace the auxiliary port by

    i=2j+1, j in Z.

Keep h,f,T,gamma,tau,y independently signed. As before, replace each of the eight positive ports x by

    x=1+u_x^2+v_x^2+r_x(r_x+1).

The final equation has 8*3+1+6=31 unrestricted integer variables. The exact original factors and all four fixed coefficients are otherwise unchanged. The resulting variants are:

* Six comparisons: 119 operations, maximum residual degree 50.
* Product equation: 127 operations, exact degree 188.
* Sum-of-squares equation: 136 operations, exact degree 100.

All counts include the substitutions: 8*7+2=58 added operations. Here 2j+1 costs a multiplication and an addition under the packet convention. The source product is 69 operations; the source system is 61 and its sum-of-squares is 78.

## Soundness

The signed-domain proof actually needs only i!=0, not i>0. Every arithmetic occurrence of i in the hybrid is through i^2. Since i=2j+1 is odd, it never vanishes; put I=|i|c^2 in the mathematical rank argument. All six-sign arguments and all congruences apply unchanged. Therefore any signed31 solution implies K215 halts and hence the existence of a finite ZFC refutation.

No arbitrary signed integer is being parametrized as odd, and no arbitrary existing solution is claimed to map to one with odd i. The converse below gives a fresh canonical auxiliary construction from a halting computation.

## Completeness with an odd ordinary-strong witness

Begin with the canonical blank-input witness from the selected compiler (the main T4 adapter, or the separate packet 06 fallback). All its word, rank, and main-Pell coordinates are unchanged. In particular,

    q=B^N is even, Y=sq^3 is even,
    a=Y(X+1) is even, A=a+2 is even,
    Delta=A^2-1 is odd,
    R=3 modulo 4, c=psi_A(R), D=chi_A(R).

For an even Pell parameter A, the recurrence psi_A(n+2)=2A psi_A(n+1)-psi_A(n), starting from 0,1, shows psi_A(n)=n modulo 2. Thus c is odd.

Change only the auxiliary strong index from the source choice 2cR to

    m=cR, f=chi_A(m), t=psi_A(m)/c^2,
    i=Delta*t, I=i*c^2=Delta*psi_A(m).

The quotient t is a positive integer. Indeed, expand

    (D+c sqrt(Delta))^c = chi_A(cR)+psi_A(cR)sqrt(Delta).

The term with one square-root factor has square-root coefficient c^2 D^(c-1); every term with at least three square-root factors is divisible by c^3. Therefore c^2 divides psi_A(cR). Since m=cR is odd, psi_A(m) is odd; c^2 is odd; hence t is odd. Delta is also odd, so i is positive and odd. Set j=(i-1)/2 in the final parametrization.

The strong relation holds exactly:

    I^2=Delta^2 psi_A(m)^2=Delta(f^2-1).

Let r=(R-1)/2, which is odd because R=3 modulo 4, and let Q_r be the integer polynomial characterized by chi_Z(2r+1)=Z Q_r(Z^2). Define

    y=psi_I(R), V=chi_I(R)/I=Q_r(I^2).

These are positive integers. The Pell norm gives

    I^2(V^2-y^2)+y^2=1.

The polynomial identities

    Q_r(1-A^2)=(-1)^r psi_A(R)=-c,
    Q_r(0)=(-1)^r R=-R

show directly that V=-c modulo f, because I^2=Delta(f^2-1)=-Delta=1-A^2 modulo f, and V=-R modulo c, because c divides I. No parity assumption on m was used in these identities.

Thus o=(V+c)/f and b=(V+R)/c are positive integers. Also f^2=1 modulo c, since psi_A(m) is divisible by c^2. From of+R=V+c+R=0 modulo c, multiply by f and use f^2=1 modulo c to get o+Rf=0 modulo c. Therefore

    T=(o+Rf)/c

is a positive integer, and

    c(Tf-1)-Rf^2=(o+Rf)f-c-Rf^2=of-c=V.

This proves that the fresh auxiliary tuple satisfies the exact compressed auxiliary formula, not merely the separated older congruences. All other comparisons and all native coefficients remain the canonical ones. A halting computation therefore yields an odd-i solution.

Combining soundness and completeness proves, formalizably in ZFC, that lack of solutions to the signed31 variants is equivalent to Con(ZFC).

## Exact degrees

Relative to the signed33 leading-form proof, i has weight 1 rather than 2, while the eight positive ports still have weight 2. The six factor weights are

    44,35,50,13,4,42.

Their sum is 188. The product's leading form before substituting i=2j+1 is

    8 Q^55 h gamma i^2 (eta+zeta)^9 w^7 s^16 T^2 f^4
      * [w(Q-F-alpha)-zQ], Q=mJ.

Replacing i by 2j+1 multiplies its leading i^2 coefficient by 4. The term selecting -zQ and eta^9 has nonzero coefficient -32m^56, and remains nonzero under the disjoint quadratic substitutions. Hence the final product degree is exactly 188. The auxiliary factor remains the unique largest residual of degree 50, giving exact SOS degree 100.

The finite emitter `build_odd_signed.py`, packets `signed31_*.json`, and `ODD_SIGNED_VALIDATION.json` verify circuit syntax, all operation counts, exact formula evaluations, and diagnostic line degrees. They supplement this proof rather than replacing the unbounded Pell/compiler/logic arguments. This is not an end-to-end proof-assistant certification or a global optimality result.
