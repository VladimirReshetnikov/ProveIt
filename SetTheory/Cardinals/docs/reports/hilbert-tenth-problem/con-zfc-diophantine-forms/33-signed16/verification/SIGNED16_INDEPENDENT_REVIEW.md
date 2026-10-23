# Independent review of the new sixteen-integer reduction

Reviewed components: the signed-j repair; linear separating weight; direct
positive-variable guards; nu=31 digit-coding identity; degree arithmetic. The
unchanged compiler, quartic-to-Jones interface and K215/refutation calibration
remain imported dependencies. This is an ordinary mathematical review, not a
kernel certificate.

## 1. Removing the j guard

With the other guards in place, b,g,s,w are positive, phi is nonnegative,
margin>0, and the source h lemma gives h>=1. The source estimates give A>1
and C>B1>0. Hence D,F are positive. E is divisible by both J and D, so
F=1 modulo J and modulo D. Thus gcd(J,F)=gcd(D,F)=1.

The retained divisibility JF | QF+J(H-C) implies F | H-C. The expression
Gp=A+F(CD+1-A) satisfies Gp=1 modulo D and Gp=A modulo F. Consequently
I=(Gp^2-1)H^2+1 is 1 modulo D and D modulo F. Therefore D,F,I are pairwise
coprime. They are positive, so DFI being a square makes each a square.

Since 0<B1<C, H=B1+jC cannot vanish for any integer j. Choose x>0 with
x^2-(Gp^2-1)H^2=1. The coefficient Gp is greater than1, so
u=Gp+sqrt(Gp^2-1) is a positive integer-coordinate Pell unit greater than1.
Some power nu^r is congruent to1 in the finite ring
(Z/CFZ)[sqrt(Gp^2-1)]: its norm is1, so it is invertible even when the
modulus shares factors with the discriminant. Therefore

    x_n+H_n sqrt(Gp^2-1)=(x+H sqrt(Gp^2-1))*nu^(rn)

has H_n=H modulo CF and tends to infinity through positive values of H_n.
The initial real factor is positive because x>|H|sqrt(Gp^2-1).
For large n, j_n=(H_n-B1)/C is a positive integer. The new I_n is a square;
D,F remain squares, and the divisibility condition is unchanged because
H_n-H is divisible byF. All other conditions are independent ofj. This
repairs every signed-j witness to a positive-j witness. The reverse existential
implication is immediate. The argument proves existential equivalence, not
pointwise equivalence of signed and positive zero sets.

## 2. Linear separating weight

Each square-stack factor is1 modulo4, so Cstar=1 modulo4 at every integer
assignment, before any inequality is inferred. Thus Cstar>=1 or Cstar<=-3.
In either case (Cstar+1)^2>|Cstar|. For Cstar>=1 the difference is
Cstar^2+Cstar+1; for Cstar<=-3 it is Cstar^2+3Cstar+1>=1.
Therefore |w1|>sqrt(|Cstar|) for w1=Cstar+1.

The bound sqrt(|(P^2-1)K^2+1|)<=P^2+K^2+1 then gives
|w2|>sqrt(|Cstar|)+|w1|sqrt(|a0|) for
w2=w1(P^2+K^2+2). The Galois sign-separation proof uses absolute values,
so negative weights cause no problem. This replacement is valid uniformly,
including invalid signed assignments which the final polynomial must reject.

## 3. Coding and guards

For nu=31, put t=5^31 and L=5^32. The coding weights are B^t followed by
B^(t-5^r), r=0,...,31. A term with exponent vector
(4-|alpha|,alpha) therefore has degree 4t-sum alpha_r5^r in B; the outside
factor B^t gives exactly L-sum alpha_r5^r. This proves the complete-
homogeneous baseline and Horner correction identity. The product of
1+T+T^2+T^3+T^4 for T=B^(5^r), r=0,...,31 is sum_{k=0}^{L-1}B^k;
multiplying by(1+B^L)(1+B^(2L)) gives the required lambda.

The six guards use discriminants 3epsilon+2,3g-1,3s-1,3w-1,3phi+2,
and3margin-1. All are2 modulo3. The stack lemma therefore enforces
exactly epsilon,phi>=0 and g,s,w,margin>0. The unrestricted h,i,j coordinates
are handled respectively by the h lemma, nonvanishing plus sign symmetry,
and the repair above.

## 4. Degree check

After five linear guards, the stack degree is363. The margin guard makes
Cstar degree2221L+1102. Thus w1 has that degree and w2 has degree
4121L+1110. The divisibility multiplier has degree34375L+107.
Combining this with deg(a1)=24640L+68 gives

    deg(A2)=101632L+2502,
    deg(P16)=4deg(A2)=406528L+10008.

The strict leading-term dominance specified by the source degree argument
and checked by the builder shows no highest-degree cancellation. This review
finds no mathematical gap in these new components.
