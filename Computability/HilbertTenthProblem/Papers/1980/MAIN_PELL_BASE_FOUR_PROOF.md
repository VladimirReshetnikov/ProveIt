# A shifted main Pell parameter and a base-four congruence: 106 operations

This note proves the positive-domain correctness of
`../verification/round14_1980_base_four_certificate.py`. Its predecessor is
the 107-operation modular-Sidon certificate
`../verification/round13_1980_certificate.py`. The encoding parameters,
including the fixed exponent L=2^32, remain those of
`MODULAR_SIDON_PROOF.md`. The change saves one addition. It has 106 core
operations, 34 positive unknowns and 22 free equality tests.

The elementary Pell facts below are those used in the corrected source
`../1982/jones1982_corrected.tex`, particularly Lemmas 2.18, 2.20, 2.22,
2.23 and 2.24 and the chi-congruence version explicitly stated after
Lemma 2.22. The signed auxiliary Pell block is justified separately in
`PELL_SIGNED_PROOF.md`. This note does not assert a newly compiled Lean
theorem. The executable certificate verifies all polynomial identities;
the argument below proves the changed analytic and positive-domain facts.

## Equations and coordinate meanings

Retain the notation

    N=n, R=r, U=w*N^2, Y=s*N^2, M=R*Y,
    a0=M*(U+1), A=a0+4, Q=U*M^2, P=2Q+1,
    J=2R+1, W=b*w, K=k, C=c.

The supplied positive input called `a` in the checker now means a0,
rather than the mathematical main Pell parameter A. Its defining
equation E12 remains

    a0=M*(U+1).

Every main Pell equation uses the mathematical parameter A=a0+4. The
first Pell equations and positive interval remain

    tau*(tau+1)=Q*(Q+1)*K^2,
    K=R+1+h*Q,
    C=K*Y+eta, K=eta+zeta, eta,zeta>0.             (1)

E14 is changed to the base-four exponential congruence

    d=W+C*(A-4)+gamma*(8A-17).                    (2)

In particular it will imply W=4^J. The other exponent congruence remains

    mu=q+kappa*(A-B)+rho*(2A*B-B^2-1).            (3)

The signed block uses G=1+(A+1)*(f^2-1), and E20 uses A-1. All these
equations are checked directly as polynomials in the supplied coordinate
a0. No computation of A is omitted from the charged instruction list:
the list never needs a register for A itself.

## Initial bounds and exact Pell indices, before exponent decoding

The unchanged positive-coefficient encoding proof establishes

    N=q^8, q>4b>=8, 3L<=B<=N<=R, b<=N, q<=N.

This is the pre-Pell bootstrap from
`POSITIVE_COEFFICIENT_BOUND_PROOF.md`; it does not assume that b or q is
a power of two. In particular N,R>=64, U,Y>=4096, M>=262144,
Q>R+1, and A>J>1. The large numerical margins here follow from the
actual q>8 and N=q^8; the weaker N>=8 bound alone would not justify
the forthcoming base-four exponent comparison.

The congruence equation in (1) gives K>=R+2. The interval gives
C/K>Y, hence C>Y*(R+2)>J. Therefore the signed Pell block, with its
generic main parameter now equal to A, yields

    C=psi_A(J), d=chi_A(J).                       (4)

Let T=2*tau+1. The triangular norm in (1) gives

    T^2-(P^2-1)*K^2=1, T>1.

Consequently T=chi_P(t), K=psi_P(t) for a positive index t. The Pell
congruence psi_P(t)=t modulo P-1=2Q also holds modulo Q. Since
0<R+1<Q, (1) therefore gives t=R+1+vQ with v>=0. If v>=1, the standard
growth bounds

    (2a-1)^m <= psi_a(m+1) <= (2a)^m

imply

    C/K <= (2A)^(2R)/(2P-1)^(R+Q)
         <= (2A/(2P-1))^(2R) < 1/2.

Indeed Q>=R and 2A/(2P-1)<1/2. For this last inequality it is enough
to observe that a0=M*(U+1)<2UM, A<2UM+4, and

    4A<8UM+16<4UM^2+1=2P-1,

using U>=4096 and M>=262144. This contradicts C/K>Y. Therefore

    K=psi_P(R+1), T=chi_P(R+1).                  (5)

This exact-index argument has not used either exponential relation,
binomial divisibility, or parity of N. It also proves h even from the
stronger congruence modulo 2Q, although that fact will not be needed.

## The shifted ratio lies strictly above the binomial expression

Put xi=(U+1)^(2R)/U^R. Applying Pell growth to (4) and (5) gives

    C/K >= (2A-1)^(2R)/(2P)^R
         =xi*(1+7/(2a0))^(2R)*(1+1/(2Q))^(-R)
         >xi.                                   (6)

For the strict inequality, the square (1+7/(2a0))^2 exceeds
1+7/a0, and 14Q>a0 implies 7/a0>1/(2Q). The inequality 14Q>a0
already follows from Q=UM^2 and a0=M*(U+1), with M>=2 and U>=1.

The upper growth estimate gives

    C/K <= (2A)^(2R)/(2P-1)^R
         <xi*(1+4/a0)^(2R)
         <xi*(1+16R/a0)
         =xi*(1+16/[Y*(U+1)]).                  (7)

To justify the last estimate explicitly, for positive t and integer m
with mt<1, binomial coefficients give

    (1+t)^m <= sum_(j>=0) (mt)^j =1/(1-mt).

Here mt=8R/a0=8/[Y*(U+1)]<1/2, so 1/(1-mt)<1+2mt.

Combining (6) with the interval C/K<Y+1 proves xi<Y+1. Since
xi>U^R, integrality gives Y>=U^R. Consequently

    a0=R*Y*(U+1)>R*U^R, and A>a0.              (8)

No exponent relation or rounding conclusion was used in establishing
this decisive size bound. In addition, xi<Y+1<2Y and (7) give

    0<C/K-xi<32/(U+1)<1/2.                     (9)

## Exponential relations and direct integral rounding

Since W=bw<=N^2*w=U and N,R>=64, (8) gives

    4^(3J)=64*64^(2R)<=64*N^(2R)<=R*U^R<A,
    W^3<=U^R<A.

The source chi version of Lemma 2.22 applied to (2) and (4), with
base V=4, now proves

    W=4^J.                                     (10)

Thus b is a power of two. Moreover

    U=N^2*w>=N*b*w=N*4^J>4*2^(2R).             (11)

The unchanged E13 gives 0<kappa<C; E19 is its Pell norm and E20
is kappa=L modulo A-1. Since 0<L<J<A, source Lemma 2.23 gives
kappa=psi_A(L), mu=chi_A(L). The pre-Pell inequalities and (8) give

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A.

Equation (3) and the same exponent lemma therefore prove q=B^L.

By (11), the binomial expansion of xi has fractional part strictly
between zero and 1/4. Its integral part F satisfies

    0<xi-F<2^(2R)/U<1/4,
    F=binom(2R,R) modulo U.                      (12)

The interval, (6), and (9) now give

    F<xi<C/K<Y+1,
    Y<C/K<xi+1/2<F+3/4.

Both Y and F are integers, so the first line gives F<=Y and the
second gives Y<=F. Hence

    Y=F, and N^2 divides binom(2R,R).             (13)

This rounding uses only integrality; parity of Y and F is unnecessary.
The power-of-two conclusions b and q are still available for the
subsequent binary no-carry decoding. With q=B^L and (13) recovered,
the remainder of the modular-Sidon encoding proof applies unchanged
and recovers a solution of the represented system of equations.

## Necessity and every changed positive witness

Start from a solution of the represented system and take the canonical
modular-Sidon coding witnesses as in the predecessor construction.
Choose the usual sufficiently large power of two b, set B=Hb^2,
q=B^L, N=q^8, and form the unchanged packed S,T,R. Its no-carry
property gives N^2 dividing binom(2R,R). These choices occur before
the Pell witnesses are selected. They supply R>=N>=64 and b<=R.

Define J=2R+1 and now choose

    w=4^J/b, U=N^2*w, Y=floor((U+1)^(2R)/U^R),
    s=Y/N^2, M=R*Y, a0=M*(U+1), A=a0+4.

The number w is a positive integer: write b=2^t; since t<=b<=R<2J,
the exponent 2J-t is positive. Bound (11) holds directly for this
choice. Expansion (12) and the central-binomial divisibility make
s integral, and Y>=U^R makes it positive.

Set Q=UM^2, P=2Q+1, C=psi_A(J), d=chi_A(J), and K=psi_P(R+1).
The lower and upper estimates (6)--(7) are purely estimates at these
chosen indices. Here xi<Y+1 follows directly from the choice of Y,
so (9) holds as well. Consequently

    Y<xi<C/K<xi+1/2<Y+3/4.

Thus eta=C-KY and zeta=K-eta are positive integers. Set

    tau=(chi_P(R+1)-1)/2,
    h=(K-R-1)/Q.

Since P is odd, the chi recurrence makes chi_P(R+1) odd; its value
is greater than one, so tau is positive integral. The Pell congruence
modulo 2Q makes h integral, and psi_P(R+1)>R+1 makes h positive.
These choices give (1), E12, and E15.

Choose positive f,i with f^2-(A^2-1)*(iC^2)^2=1, as in the source
Pell construction. For completeness this existence is the same
standard divisibility construction used in `PELL_SIGNED_PROOF.md`;
it holds for every A>1 and positive C=psi_A(J), so adding four to
A creates no additional hypothesis. Put

    G=1+(A+1)*(f^2-1), I=chi_G(J), H17=psi_G(J),
    o=(I+d)/f, j=(H17-J)/C.

The congruences G=-A modulo f and G=1 modulo C, together with odd
J, show that these are integers. Both are positive, since I+d>0
and psi_G(J)>J. They give the signed E17 with of-d=I.

Choose kappa=psi_A(L), mu=chi_A(L),
Delta=(kappa-L)/(A-1), and phi=C-kappa. As J>L>=2, Pell growth
and congruence show that Delta and phi are positive integers.

The exponential congruence lemma supplies integer quotients gamma
and rho in (2) and (3). Their positivity follows explicitly, rather
than from merely knowing a congruence. The identity

    chi_A(t)=A*psi_A(t)-psi_A(t-1)

and 0<psi_A(t-1)<psi_A(t) give

    d-(A-4)C=4C-psi_A(J-1)>3C>W,
    mu-(A-B)kappa=B*kappa-psi_A(L-1)>(B-1)kappa>q.

For the last comparisons, (8) gives A>W^3 and A>q^3; since J,L>=2,
the Pell denominators C,kappa are at least A. Both moduli 8A-17
and 2AB-B^2-1 are positive because A>B>=2 and A>4. Thus gamma
and rho are positive. All other coding witnesses, including the
positive Omega and sigma, are exactly those of the established
modular-Sidon construction. This completes necessity.

This proof constructs new w,s,a0 and all dependent Pell coordinates.
It does not claim that the old base-two value of w can be preserved
under the new base-four exponent equation.

## Exact global arithmetic and the numeral convention

The existing third mask already computes B-4. With the supplied a0,
the main Pell expressions are evaluated as

    A-4=a0,
    A-1=a0+3,
    A+1=(A-1)+2,
    A^2-1=(A-1)*(A+1),
    8A-17=8*a0+15,
    A-B=a0-(B-4).

The old subtraction computing a-2 disappears. The other displayed
expressions cost exactly as many operations as their predecessor
counterparts, and E12 still uses the same two-register factorization
of M*(U+1). The complete schedule therefore has 59 multiplications
and 47 additions, totaling 106. The input named a remains positive;
there are still 34 positive unknowns and 22 free equality tests.

The verifier checks every expanded source residual, including the
unchanged E7 triangular correction and the E17 correction with A+1,
as well as each serialized addition or multiplication. It separately
checks all shifted-register identities. Subtraction is serialized as
a reversed addition with an allowed signed auxiliary register, under
the same certificate model as every predecessor.

The accompanying initial strict certificate constructs the additional
numerals 3=2+1, 8=4+4, and 15=16-1 using three instructions beyond
the predecessor's six-instruction chain. It therefore has 115 total
instructions when all fixed numerals must be generated from one.
This is an explicit valid strict certificate, not an improvement over
the separate 113-instruction strict milestone. The improved claim
here concerns the user's core measure with fixed numerals supplied.
