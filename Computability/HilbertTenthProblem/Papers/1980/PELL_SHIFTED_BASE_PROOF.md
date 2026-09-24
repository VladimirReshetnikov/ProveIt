# One operation saved by shifting the first Pell parameter

This note proves a 113-operation successor to the 114-operation system in
`../verification/round5_1980_certificate.py`. Its executable companion is
`../verification/round5_1980_shifted_pell_certificate.py`.

Write

    N=n, R=r, U=wN^2, Y=sN^2, M=RY, A=a=M(U+1),
    X=2UM^2, P=X+1, K=k, C=c, J=2R+1, W=bw.

The previous first Pell parameter was p=X. Remove the positive unknown p
and its defining equality E8. Replace E9 and E11 by

    X(X+2) K^2+1=tau^2,
    K=R+1+hX.

The first equation is exactly the Pell equation with parameter P=X+1,
because P^2-1=X(X+2). The second is K=R+1+h(P-1). Retain all other
equations, including the strict positive interval

    C=KY+eta, K=eta+zeta, eta,zeta>0,

which says 0<C/K-Y<1. The mathematical value P is neither a new witness
nor an additional computed value. The existing instruction R8 computes
X. Evaluating X+2 and X(X+2) costs the same two operations as the former
p^2 and p^2-1. The former subtraction p-1 disappears, saving one operation.

The shift changes the Pell approximation, so it requires an argument
beyond the polynomial identity. The proof below establishes exact
existential equivalence under the same admissible encoding parameters.
It re-chooses k,tau,h,eta,zeta and removes or restores p, preserving every
other witness. It uses the elementary Pell lemmas of the corrected source
and the separately proved signed Pell block; it asserts no new Lean result.

## Initial growth and exact Pell indices

The short-mask decoding proof, independent of E8--E20, gives

    3<3L<=B<q<=N<=R, N=q^8, N>=8, R>=8, b<=N,

where B=H b^4. Admissibility makes H a power of two greater than one,
so B is even already. No parity of q or N is assumed at this stage.
We therefore have U,Y>=64, M>=512 and A>=33280.

Since h>0, the modified E11 gives K>=R+2. The interval gives

    C>(Y-1)K>=63(R+2)>J.

Thus the hypotheses of `PELL_SIGNED_PROOF.md` hold, independently of any
Pell approximation or rounding conclusion. E15--E17 imply

    C=psi_A(J), d=chi_A(J).

The modified E9 gives K=psi_P(t) for a positive integer t. The elementary
Pell congruence psi_P(t)=t modulo P-1 and E11 imply

    t=R+1+vX, v>=0,

because X>R+1. If v>=1, the elementary growth bounds

    (2a-1)^m <= psi_a(m+1) <= (2a)^m

give

    C/K <= (2A)^(2R)/(2P-1)^(R+X)
         <= (2A/(2P-1))^(2R) < 1/2.

Here X>=R and

    2A/(2P-1)=2M(U+1)/(4UM^2+1)<1/2;

the latter follows immediately from U>=64 and M>=512. This contradicts
C/K>Y-1>=63. Consequently

    K=psi_P(R+1), tau=chi_P(R+1).

## Perturbed ratio estimate and a bound for A

Put xi=(U+1)^(2R)/U^R. Applying the same growth bounds at the two exact
indices gives the particularly useful strict upper bound

    C/K <= (2A)^(2R)/(2P-1)^R
         = xi*(1+1/(4UM^2))^(-R) < xi.             (1)

For the lower bound they give

    C/K >= (2A-1)^(2R)/(2P)^R
         = xi*(1-1/(2A))^(2R)*(1+1/X)^(-R)
         > xi*(1-R/A)*(1-R/X)
         > xi*(1-R/A-R/X).                        (2)

The two factors in the penultimate line are positive. Bernoulli's
inequality justifies the first factor estimate; the elementary convex
inequality (1+t)^(-R)>1-Rt for t>0 justifies the second. Define

    epsilon=R/A+R/X.

Since A/X=(U+1)/(2UM)<1/M<1, we have

    epsilon < 2R/A = 2/[Y(U+1)] < 1/2.            (3)

It follows that

    C/K > xi/2 > U^R/2 > U^(R-1)+1.

The last strict inequality uses only U>=64 and R>=8. Combining it with
C/K<Y+1 yields

    Y>U^(R-1), hence A=RY(U+1)>R U^R.             (4)

In particular, no rounding argument and no parity of N has been used
to establish (4).

## Recover the exponential relations before using parity

The following repeats the necessary exponent-lemma argument with the new
bound (4); it does not apply the old approximation lemma with a changed
hypothesis. Since N>=8, R>=8 and W=bw<=U,

    2^(3J)=8*8^(2R)<=8*N^(2R)<=R U^R<A,
    W^3<=U^R<A.

The unchanged E14, together with C=psi_A(J) and d=chi_A(J), is the chi
congruence from the corrected source Lemma 2.22 for base 2. The two strict
size inequalities therefore give

    W=2^J.

In particular b is a power of two and

    U=N^2w>=Nbw=NW>=8*2^J>4*2^(2R).              (5)

E13 gives 0<kappa<C; E19 is its Pell equation and E20 gives
kappa=L modulo A-1. The initial bounds imply 0<L<J<A. The source
Lemma 2.23 therefore gives

    kappa=psi_A(L), mu=chi_A(L).

Also, by the initial bounds and (4),

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A.

The unchanged E18 and the chi version of Lemma 2.22 now give

    q=B^L.

Since admissibility already made B even, q and N=q^8 are now even.
This proves exactly the parity needed next, without first assuming
central-binomial divisibility or its rounding characterization.

## Parity rounding with the perturbed error

From xi/2<C/K<Y+1 and Y>=64, we have xi<2Y+2<3Y. Equations (1)--(3)
then yield

    0<xi-C/K<xi*epsilon
       <2xi/[Y(U+1)]<6/(U+1)<=6/65<1/4.          (6)

By (5), the binomial expansion from source Lemma 2.24 gives

    0<xi-floor(xi)<2^(2R)/U<1/4,
    floor(xi)=binom(2R,R) modulo U.              (7)

Together with the positive interval, these imply

    |Y-floor(xi)|<1+1/4+1/4<2.

Both integers in this difference are even: Y=sN^2 and U=wN^2 are even,
and binom(2R,R)=2*binom(2R-1,R-1) is even, so (7) makes floor(xi) even.
It follows that

    Y=floor(xi), and N^2 divides binom(2R,R).     (8)

These are the same no-carry conclusions as for the 114-operation system.
After (8), (7) also gives xi<Y+1/4<2Y, improving (6) to

    0<xi-C/K<4/(U+1)<4/U.                       (9)

## Necessity: the new interval witnesses are positive

Start with any solution of the established 114-operation system.
Its parity and interval proofs give C=psi_A(J), (5), (7), (8), and
xi<2Y. Keep U,Y,M,A,C and every witness except p,k,tau,h,eta,zeta.
Remove p and set

    K_new=psi_(X+1)(R+1), tau_new=chi_(X+1)(R+1),
    h_new=(K_new-R-1)/X.

The Pell congruence makes h_new integral, and strict growth
psi_(X+1)(R+1)>R+1 makes it positive. E9 and E11 hold by construction.
The exact-index estimates (1)--(3), now using xi<2Y directly, give (9)
for this new K.

The positive fractional tail in the binomial expansion contains the
term binom(2R,R-1)/U. Because its entire tail is less than one, (8)
implies

    xi-Y>=binom(2R,R-1)/U>=2R/U>4/U.             (10)

The middle inequality is elementary unimodality: every binomial
coefficient from positions 1 through 2R-1 is at least 2R. Subtracting
(9) from (10) proves C/K_new>Y. Equation (1) and (7) give
C/K_new<xi<Y+1/4<Y+1. Thus the integers

    eta_new=C-K_new*Y,
    zeta_new=K_new-eta_new

are both positive. This constructs all changed witnesses explicitly.

## Recovering the old system

Conversely, start with a solution of the new 113-operation system. The
preceding noncircular sufficiency proof gives (5), (7), (8) and xi<2Y.
Restore p=X and define

    K_old=psi_X(R+1), tau_old=chi_X(R+1),
    h_old=(K_old-R-1)/(X-1).

Again the Pell congruence and strict growth make h_old a positive
integer. For completeness, the old exact-index growth estimates give

    xi*(1-R/A)<C/K_old<xi*(1+R/X).               (11)

For the upper estimate, first bound the ratio by
xi*(1-1/(2X))^(-R). Bernoulli gives
(1-1/(2X))^R>=1-R/(2X), and R/(2X)<1/2 gives
(1-R/(2X))^(-1)<1+R/X. The lower estimate follows directly from
(1-1/(2A))^(2R)>1-R/A. In particular, because A<X and xi<2Y,

    |C/K_old-xi|<xi*R/A<2/(U+1)<2/U.

The positive tail (10) exceeds this error, so C/K_old>Y. Also

    C/K_old-Y<1/4+2/U<=1/4+1/32<1.

Therefore eta_old=C-K_old*Y and zeta_old=K_old-eta_old are positive
integers. The old E8--E11 are now satisfied; every other witness and
equation has been preserved. This proves both directions of existential
equivalence, with the positivity of every altered witness justified.

## Exact arithmetic and accounting boundary

The executable certificate has 50 additions and 63 multiplications,
113 operations in total, with 32 positive unknowns and 20 free equality
tests. Constructing the numerals 2,4,5 and L=5^64 from 1 costs the same
nine additional instructions as before, giving 122 under that convention.
The admissible encoding parameters x,Z,V,H remain supplied inputs.

The verifier independently expands every equation residual and verifies
every serialized addition or multiplication, including reversed additions
used to represent subtraction with signed auxiliaries. The unchanged E7
and E17 triangular residual corrections are checked against their new
array positions after E8 is removed. The JSON contains the full primitive
list, equality list, input domains, expanded residual polynomials,
corrections and numeral chain. These are exact algebraic verifications;
positive-domain equivalence relies on the argument above.
