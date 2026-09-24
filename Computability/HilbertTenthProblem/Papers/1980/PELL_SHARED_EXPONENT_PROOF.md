# Share the binomial scale with the exponential witness: 103 operations

This note proves the 103-operation certificate
`../verification/round21_1980_shared_exponent_certificate.py`. Its
predecessor is the 104-operation shared-norm construction in
`PELL_SHARED_RATIO_PRODUCT_PROOF.md`. The fixed index is unchanged from
`MODULAR_SIDON_PROOF.md`. All fixed numerals are supplied free.

The old definitions `U=wN^2` and `W=bw` used two multiplications.
Replace both by the shared positive value

    U=W=Bw, B=Hb^2.                             (1)

Change the first index modulus to another value already calculated
for the norm. This requires new proofs of the exact index, the initial
size bounds and the final divisibility by N^2. The argument below
supplies them; it never assumes the discarded identity U=wN^2.

The elementary Pell lemmas are those in the corrected source
`../1982/jones1982_corrected.tex`. The signed block is justified by
`PELL_SIGNED_PROOF.md`. The new proof is mathematical; no newly compiled
Lean theorem is asserted. The exact checker verifies every primitive
instruction and source residual separately.

## Equations and the parity of the packed index

Use the notation

    N=n, R=r, U=Bw, Y=sN^2,
    a0=Y(U+1), A=a0+4,
    Q=UY^2, P=2Q+1, E=U(Q+1)=(UY)^2+U,
    J=2R+1, K=k, C=c.

The positive supplied coordinate named `a` remains a0. Neither Q nor P
is a calculated or supplied register. E is the existing calculated
coefficient in the shared norm. The first Pell equations become

    tau(tau+1)=Q(Q+1)K^2=( (UY)^2+U )(YK)^2,
    K=R+1+hE, h>0,
    C=KY+eta, K=eta+zeta, eta,zeta>0.             (2)

The first exponent congruence is now

    d=U+C(A-4)+gamma(8A-17).                     (3)

All remaining equations are unchanged as polynomials in the supplied
coordinates, apart from the definitions of U and a0 propagated into
the first norm and index equation. In particular, the second exponent
congruence still uses base B and target q.

The fixed index V is even. Indeed, the support code ell_0 has only
positive weights, its evaluation at the even number Z is even, and
the other term in V is multiplied by Z^L with L>0. Also B and Z are
even, so theta=B-Z is even. The packed congruence therefore gives

    ell+eq=V+t theta=0 modulo2.                 (4)

We claim that R is even before invoking any Pell or exponent equation.
If q is odd, N=q^8 is odd, and both N^2-N and N^2-1 are even. The
defining expression for R is then even. If q is even, (4) makes ell
even. Every term of

    T+1=q^2(1+theta lambda)-(b-1)ell+(B-4)ell q^4

is even. Again

    R=S(N^2-N)+(T+1)(N^2-1)

is even. Consequently R+1 is odd in every positive solution of the
coding equations. This parity argument does not assume b or q to be
a power of two and does not use the no-carry conclusion.

## Initial bounds and the exact first Pell index

The unchanged coding bootstrap gives

    N=q^8, q>4b>=8, 3L<=B<=N<=R, b<=N,
    0<S<N, 0<=T<N, R<2N^3.

Thus N,R>=64 and Y>=N^2. The fixed admissibility bound on H gives
B>4096; hence the new U=Bw satisfies U>=B>4096. We do not assume
U>=N^2. In particular,

    Q=UY^2>=Y^2>=N^4>6N^3+1>3R+1.             (5)

Equation (2) gives K>=R+2, and its interval gives C>YK>J. The signed
Pell block requires only A>1, 1<J<C and odd J. These hypotheses hold,
so it yields

    C=psi_A(J), d=chi_A(J).                      (6)

An initial inequality J<A is unnecessary here: it is not a hypothesis
of the signed block, and will be proved later before it is needed.

Set T_Pell=2tau+1. The norm in (2) is the ordinary positive Pell
equation with parameter P, so

    K=psi_P(t), T_Pell=chi_P(t)

for a positive integer t. Modulo Q+1, the parameter P is -1. The
integer-polynomial Pell recurrence therefore gives

    psi_P(t)=(-1)^(t-1)t modulo(Q+1).

The index equation in (2), and the fact Q+1 divides E, imply

    t=R+1 or -(R+1) modulo(Q+1),                 (7)

with the sign determined by the parity of t. Since Q+1>2(R+1),
every positive t satisfying (7), other than R+1 itself, is at least

    Q+1-(R+1)=Q-R>2R+1.

For any such t, elementary Pell growth gives

    C/K <= (2A)^(2R)/(2P-1)^(t-1)
         < (2A/(2P-1))^(2R) < 1/2.

The last bound follows explicitly from

    (2P-1)-4A=4Y[U(Y-1)-1]-15>0,

using U,Y>=4096. This contradicts C/K>Y. Thus the first index is

    K=psi_P(R+1), T_Pell=chi_P(R+1).             (8)

No exponential relation, approximation error bound, or assumption
U>=N^2 has entered this argument.

## Use the lower ratio before estimating the error

Let xi=(U+1)^(2R)/U^R. At the exact indices (6) and (8), the same
principal cancellation and lower growth estimate give

    C/K >= xi*(1+7/(2a0))^(2R)*(1+1/(2Q))^(-R)
         > xi.                                  (9)

For strictness, 14Q>a0 holds for Q=UY^2 and a0=Y(U+1), and hence
(1+7/(2a0))^2>1+1/(2Q). This lower estimate requires no bound on
8R/a0. Combined with the positive interval it gives

    xi<Y+1, Y>=U^R,
    a0=Y(U+1)>U^(R+1), A>a0.                   (10)

Here Y>=U^R follows from integrality and xi>U^R. In particular
A>2^(R+1)>2R+1=J, supplying the inequality deferred above.

Because U>=4096 and U>64,

    4^(3J)=64*4096^R<=64U^R<U^(R+1)<A,
    U^3<=U^R<A.

The source chi-congruence exponent lemma applies to (3), with base4,
target W=U and denominator C=psi_A(J). It proves

    U=4^J.                                     (11)

Thus B, as a positive divisor of U=Bw, is a power of two. Since
B=Hb^2 and H is a power of two, b is also a power of two.

Only now estimate the approximation error. The upper growth bound is

    C/K<xi*(1+4/a0)^(2R).

Equation (10), together with U=4^J and R>=64, implies
8R/a0<1/2. Applying (1+t)^m<=1/(1-mt)<1+2mt with
t=4/a0 and m=2R therefore gives

    C/K<xi*(1+16R/a0).

Since xi<Y+1<2Y, this yields

    0<C/K-xi<32R/(U+1)<1/2.                    (12)

The last inequality follows from U=4^(2R+1)>64R for R>=64. This
ordering avoids reusing the old pre-exponent bound U>=N^2, which
is absent in the present system.

## The second exponent and the required divisibility

The positive gap C>kappa, its Pell norm and its congruence modulo
A-1 now identify kappa=psi_A(L), mu=chi_A(L), because
0<L<J<A. For the source exponent lemma we have

    B^(3L)<=B^B<=U^R<A,
    q^3<=N<=R<U^R<A.

The first line uses 3L<=B<=R and B<=U. The second uses N=q^8,
q>=1 and U>=2. The unchanged second chi congruence consequently
gives q=B^L. Thus q and N are powers of two.

We must now recover the divisibility formerly built into U=wN^2.
Both N^2 and U=4^J are powers of two, and

    N^2<=R^2<=4^R<4^(2R+1)=U.

Therefore N^2 divides U. This follows after exponent decoding; it
was not assumed in any earlier step.

The binomial expansion has integer part F with

    0<xi-F<2^(2R)/U<1/4,
    F=binom(2R,R) modulo U.

From (9), (12), and the interval,

    F<xi<C/K<Y+1,
    Y<C/K<xi+1/2<F+3/4.

Integrality gives Y=F. Since N^2 divides both Y=sN^2 and U, it
follows that N^2 divides binom(2R,R). The established power-of-two
and no-carry conclusions now give the original represented system
by the unchanged modular-Sidon decoding. This proves sufficiency.

## Necessity and all positive witness choices

Start with a solution of the represented system. Use its canonical
modular-Sidon coding witnesses, choosing b a sufficiently large power
of two and setting B=Hb^2, q=B^L, N=q^8. Form the same packed S,T,R.
They give R>=N, the no-carry central-binomial divisibility and, by the
parity argument above, even R.

Choose

    J=2R+1, U=4^J, w=U/B,
    Y=floor((U+1)^(2R)/U^R), s=Y/N^2,
    a0=Y(U+1), A=a0+4,
    Q=UY^2, P=2Q+1, E=U(Q+1),
    C=psi_A(J), d=chi_A(J), K=psi_P(R+1).

The quotient w is positive integral because B and U are powers of
two and B<=N<=R<U. The preceding power comparison also gives
N^2 dividing U. The binomial expansion and central-binomial
divisibility make s positive integral. The lower and upper ratio
estimates at these chosen indices, with Y=floor(xi), give

    Y<xi<C/K<xi+1/2<Y+3/4.

Thus eta=C-KY and zeta=K-eta are positive integers. The odd parameter
P makes chi_P(R+1) odd and greater than one, so

    tau=(chi_P(R+1)-1)/2

is a positive integer.

The new quotient h requires both moduli. Since P=1 modulo U,
K=R+1 modulo U. Since P=-1 modulo Q+1 and R+1 is odd,
K=R+1 modulo Q+1. Also gcd(U,Q+1)=1, as Q=UY^2. Hence

    h=(K-R-1)/(U(Q+1))

is an integer. It is positive by strict Pell growth K>R+1.
This establishes the stronger congruence needed for necessity;
the congruence modulo Q+1 alone would not suffice for this quotient.

Choose the remaining main Pell witnesses by the same generic
constructions at the new A. Choose positive f,i with
f^2-(A^2-1)(iC^2)^2=1, and set

    G=1+(A+1)(f^2-1), I=chi_G(J), H17=psi_G(J),
    o=(I+d)/f, j=(H17-J)/C.

The congruences G=-A modulo f, G=1 modulo C, and odd J make o,j
positive integers and give of-d=I, as proved in the signed-block
construction. Choose kappa=psi_A(L), mu=chi_A(L),
Delta=(kappa-L)/(A-1), and phi=C-kappa. Their positivity follows
from 2<=L<J and the usual congruence and strict growth.

The two exponent congruences give integer gamma and rho. Their
positivity follows from

    d-(A-4)C=4C-psi_A(J-1)>3C>U,
    mu-(A-B)kappa=B*kappa-psi_A(L-1)>(B-1)kappa>q.

Here A>U^3 and A>q^3 follow from (10) and the size comparisons above;
C,kappa>=A because J,L>=2. Both moduli are positive. All positive
coding witnesses, including Omega and sigma, are unchanged. Thus
every new positive witness is constructed, establishing necessity.

## Exact arithmetic saving

Replace the old instruction U=wN^2 by U=Bw, at the same cost.
Delete the old instruction W=bw and use U in the base-four congruence.
Replace the index product h(UY) by hE, where E=(UY)^2+U is already
computed for the shared norm. That replacement has the same cost.

No additional instruction is needed. The count decreases from104
to103 by one multiplication, giving 56 multiplications and47
additions. There are still34 positive unknowns and22 equality tests.

The exact checker verifies every primitive, all source residuals and
both triangular corrections, the shared values U and E, and the
absence of the separate exponential-witness product. It checks that
only E9,E11,E12,E14 change as expanded source polynomials. Its parity
enumeration is a supplementary check; the all-integer parity proof
required by the theorem is given above.
