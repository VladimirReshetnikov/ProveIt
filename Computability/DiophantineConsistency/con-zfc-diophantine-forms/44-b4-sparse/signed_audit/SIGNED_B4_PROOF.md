# Fourteen unrestricted integers with the B4 fixed-polynomial front end

The complete arithmetic circuit is generated/signed14_b4.json. It has exactly 14 unrestricted integer variables, 1420 live binary operations (492 additions, 23 subtractions, 905 multiplications), and exact total degree

 370432t+84456 = 226295141096, where t=610895.

This is not a new unrestricted-integer variable-count record; the companion Sun construction uses ten. It is a much lower-degree and slightly shorter concrete fourteen-integer Jones instance than the previous fourteen-integer packages.

## Coefficients and coding

Use exactly the whole coefficient tuple and the 31-variable quartic from ../sun/sources/data/INSTANCE.json and its referenced payloads. The sparse c_alpha records are ../sun/sources/data/constants.json; they are independently reconstructed from the shifted sum of squares. The fixed z bound is 2^4269855. Set a=2^4269877. Then a>2z32^4 and a>2048z; its exponent is odd. Unlike the old cofinal scale, this integer has only 4,269,878 bits and can be materialized if desired.

Use the 31 positive B4 weights from ../root_checks/bose_chowla_31_optimized.json, whose zero-padded four-sum certificate contains 52,360 distinct sums. The maximum is610895. All constants are finite explicit recipes, not parameters or additional unknowns.

The variables are

 (epsilon,g,h,s,w,phi,i,j,z1,z2,z3,z4,residue,normroot).

Set b=2 epsilon^2, B=a b^4, and omega=w^2. Define R,N,Gcap by FIXED_POLYNOMIAL_CARRY_PROOF.md. The entire ordinary universal proof of this front end is given there, including the signed digit polynomial, arbitrary-position mask, coefficient extraction, binary shifted carry, unconditional R positivity, all packing bounds, and completeness for arbitrarily large odd base exponents.

## The unchanged literal ratio registers

U=N^2 omega, Y=N^2 s, M=RY, P=2M^2U,
K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=b omega,
C=B1+W1+phi, J=4A-5, Q=3W1 C-2(W1^2-1),
D=(A^2-1)C^2+1, E=iJDC^2, F=(A^2-1)E^2+1,
G=A+F(CD+1-A), H=B1+jC, I=(G^2-1)H^2+1,
a0=(P^2-1)K^2+1, a1=DFI,
m=K^2Gcap-4(C-KY)^2Gcap-8gK^2,
Ddiv=JF, Tdiv=QF+J(H-C).

The literal ratio theorem is used only with its stated hypotheses: R,N>=8, 0<b<=N<=R, Gcap>0, g,h,s,omega,i,j positive, phi nonnegative. Its square/divisibility/margin conditions recover b a power of two, N^2|binomial(2R,R), and 8g<Gcap. Completeness needs32g<Gcap, supplied by the exact digit code.

## Four sign guards in one square

Let d1=3g-1,d2=3s-1,d3=3phi+2,d4=3m-1, and set

 C0=1, Bj=1+4dj C_(j-1) zj^2, Cj=C_(j-1)Bj, Cstar=C4.

Each Bj and Cj is1 modulo4, and gcd(Bj,C_(j-1))=1. If all zj are nonzero and Cstar is a square, unique factorization makes every |Bj| a square. A negative square cannot be1 modulo4, so every Bj>0 and every prefix Cj>0. Since dj=2 modulo3 it is nonzero; dj<0 would now imply Bj<=-3, impossible. Hence g,s>=1, phi>=0 and m>0.

Conversely these four inequalities make each dj positive and nonsquare. Inductively C_(j-1) is a positive square, so dj C_(j-1) is positive nonsquare. A nontrivial Pell solution u^2-dj C_(j-1)v^2=1 can be chosen with v even, by taking a suitable positive power of a fundamental unit modulo2. Set zj=v/2. Then Bj=u^2 and Cj is a square. Every zj is nonzero.

For any signed assignment with all zj nonzero, each prefix Cj is 1 modulo 4 and hence nonzero, and each dj is 2 modulo 3 and hence nonzero. Thus Bj=1+4dj C_(j-1)zj^2 is not 1. Since Bj is 1 modulo 4, it is also neither 0 nor -1, so |Bj|>=3. Consequently |Cstar|>1 unconditionally, before the square or positivity conditions have been recovered.

## Divisibility and all nonvanishing conditions

Set Z=epsilon w i z1z2z3z4 and

 S=Z Ddiv^5,
 r=Tdiv+Ddiv residue,
 T=(r^3-Ddiv^2r-Ddiv^3)(r^2+23Ddiv^2).

For every integer assignment Ddiv!=0: J=4A-5!=0; if F=0, integer factorization forces A=0,E=+/-1, while E is divisible by J=-5, a contradiction.

The polynomial Pi(x)=(x^3-x-1)(x^2+23) has no rational root and a root modulo every positive integer. For odd primes other than23, either the cubic has a simple root or its irreducible Frobenius three-cycle makes its discriminant -23 a square, so the quadratic has a simple root. Lift by Hensel. At23 the cubic's root3 is simple. At2, -23=1 modulo8 has compatible square roots modulo all powers of2. Apply CRT.

It follows that for D!=0,

 D|T0 and Z!=0 iff some v has ZD^5 | D^5 Pi(T0/D+v).

For the forward direction choose a root of Pi modulo|Z|. For the reverse, a prime p with alpha=v_p(D)>beta=v_p(T0) would give v_p(r)=beta and valuations3beta and2beta in the two factors, hence5beta<5alpha, impossible. Z=0 would require the nonzero numerator to vanish. Consequently S|T is exactly the original divisibility Ddiv|Tdiv together with every needed nonzero condition. The numerator T never vanishes, since Pi has no rational root.

## Three-root final polynomial

Set w1=Cstar, w2=Cstar(P^2+K^2+2), X=S normroot-T and

 A0=S^2Cstar, A1=S^2w1^2a0, A2=S^2w2^2a1,
 V=X^2+A2-A0-A1, W=V^2+4X^2A2-4A0A1,
 F14=W^2-16V^2X^2A2.

This is the product over the eight signs of

 X-S(e0 sqrt(Cstar)+e1 w1 sqrt(a0)+e2 w2 sqrt(a1)).

The identity is purely polynomial and holds with complex roots. If S=0, F14=T^8!=0. Thus every zero has S!=0 and all guard variables nonzero. Then |w1|>sqrt(|Cstar|), while the elementary bound

 sqrt(|(P^2-1)K^2+1|)<=P^2+K^2+1

implies |w2|>sqrt(|Cstar|)+|w1|sqrt(|a0|). In a sign change the largest changed nonzero radical dominates the sum of all earlier ones in complex absolute value. Therefore distinct effective sign patterns have distinct sums, even with negative radicands or repeated square classes. If one sum is rational, all automorphisms of its multiquadratic splitting field must fix each individual root; those roots are rational and hence integers. The product vanishing therefore implies Cstar,a0,a1 are integer squares and S|T. Conversely those square and divisibility conditions supply an integer normroot making a factor zero.

## Equivalence and sign recovery

At an F14 zero the stack gives g,s>=1,phi>=0,m>0; the merger gives epsilon,w,i!=0. Thus b>=2 and omega>=1. The margin gives8g<Gcap, so the front-end bounds give R>=N>=8 and b<=N<=R. The strict approximation4(C-KY)^2<K^2, with C,Y>0, gives K>0. If h<=0 then1<=K<=R+1<P. K=1 would imply P-1|R, impossible. For2<=K<P,

 (PK-1)^2 < (P^2-1)K^2+1 < (PK)^2,

contradicting a0 square. Hence h>=1. Replace i by|i| without changing any condition.

To make j positive, F|H-C and the congruences F=1modD, G=1modD, G=AmodF give pairwise coprimality of positive D,F,I. Thus all are squares. Let d=G^2-1>0, x=sqrt(I). The unit x+Hsqrt(d) is positive even for H<0. A positive power of G+sqrt(d) is1 modulo CF. Multiplying by arbitrarily large such powers gives integer Pell solutions with H' congruent to H modulo CF and H'>B1. Set j'=(H'-B1)/C>0. All ratio conditions persist. This yields the genuine positive ratio interface, and the new carry proof recovers a natural zero of the source quartic.

Conversely a quartic zero admits a direct code at any sufficiently large b=2^(1+2r). Set epsilon=2^r. Jones's actual canonical witness has omega=2^(2R+1-k), a positive square because k is odd. Take its integer square root w; all four guards hold. The stack supplies zj, the intersective merger supplies residue, and the norm supplies normroot. This proves F14 has an integer zero iff the source quartic has a natural zero, hence iff there is a finite ZFC refutation. Negation gives the claimed Con(ZFC) equivalence inside ZFC.

## Exact degree and checks

Degrees in t are: R=216t+48, P=864t+196, K=864t+197, a0=3456t+786, a1=22464t+5090, m=2024t+462, Cstar=2024t+506, Ddiv=6264t+1421, S=31320t+7112, w2=3752t+900, A2=92608t+21114. A2 strictly dominates X^2,A0,A1, and the output has leading term A2^4. The sparse symbolic diagonal-head computation tracks ALL fixed coefficient leaves; its final surviving monomial is a nonzero scalar times a power of base_scale, with no unspecified coefficient specialization. Thus370432t+84456 is the exact total degree, not only an upper bound.

Run build_signed_b4.py and check_signed_b4.py. The checker independently evaluates the literal source sum, all ratio/finalizer registers, and the expanded eight-factor norm at150 signed assignments over three primes; reconstructs all source quartic coefficients and authenticates the actual fixed ports; checks all52,360 B4 sums; and exercises the carry front end with exact large-integer toy witnesses. These finite checks supplement the universal proof and do not replace the unchanged compiler/machine theorem or constitute a new Lean certificate.
