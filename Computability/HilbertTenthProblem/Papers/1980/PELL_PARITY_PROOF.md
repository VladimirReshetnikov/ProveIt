# One operation saved by parity in the Pell approximation

This proves the sufficiency of replacing E10 by

    (c-k s n^2)^2+eta=k^2, eta>0.

It saves the multiplication by 4 in the 119-operation certificate,
giving 118 operations. The companion verifier is
`../verification/round4_1980_parity_optimized_certificate.py`.
The argument below re-proves the required part of Lemma 2.25 with
the weaker bound. It does not invoke the original lemma while its
stronger hypothesis is unavailable.

## Initial facts, independent of the Pell approximation

The packed-code bounds, proved without using E8--E20, give

    3<3L<=B<q<=N<=R, N=q^16, N>=8, R>=8, 0<b<=N<=R.

Here B=H b^4, and admissibility fixes H as a power of two greater
than 1. Thus B is already even, independently of whether b is a
power of two. We do not yet assume q or N is even.

Use the dictionary

    N=n, R=r, Y=sN^2, U=wN^2, M=RY,
    A=a=M(U+1), P=p=2UM^2, K=k, C=c, J=2R+1, W=bw.

Consequently U,Y>=64, M>=512 and A>=33280. The weakened E10 says

    |C/K-Y|<1.                                      (w)

E11 gives K=R+1+h(P-1)>=R+2. Therefore
C>(Y-1)K>=63(R+2)>J. E15--E17, with the original or the alternate
Pell parameter, now satisfy the hypotheses of Corollary 2.29 and
give C=psi_A(J). The positive first coordinate is d=chi_A(J).
This use of Corollary 2.29 is independent of any rounding conclusion.

## Determine the index of K

E9 gives K=psi_P(t) for a positive integer t. The elementary Pell
congruence psi_P(t)=t modulo P-1 and E11 imply

    t=R+1+v(P-1), v>=0,

since 0<R+1<P-1. If v>=1, the bounds of Lemma 2.19 give

    C/K <= (2A)^(2R)/(2P-1)^(R+P-1)
         <= (2A/(2P-1))^(2R) < 1/2.

The last comparison follows from M>=512,U>=64 and
2A/(2P-1)=2M(U+1)/(4M^2U-1)<1/2. This contradicts
C/K>Y-1>=63. Hence

    K=psi_P(R+1).

Put xi=(U+1)^(2R)/U^R. The same applications of Lemma 2.19 and
the elementary inequalities 2.17 as in the source now yield

    xi(1-R/[M(U+1)]) < C/K
      < xi(1+R/[2M^2U]).                            (1)

These estimates use only the just established exact Pell indices.
They do not use the factor 4 in the old approximation condition.

Since R/[M(U+1)]=1/[Y(U+1)]<1/2 and xi>U^R,

    C/K > xi/2 > U^R/2 > U^(R-1)+1.

The last strict inequality holds for U>=64,R>=8. Combining it
with (w), which gives C/K<Y+1, shows

    Y>U^(R-1), and hence A=RY(U+1)>R U^R.          (2)

## Recover both exponential relations before rounding

First, (2) and N>=8 give

    A > R U^R >= 8 N^(2R) >= 8*8^(2R)=2^(3J).

Since W=bw<=N^2w=U and R>=8, also W^3<=U^R<A.
The congruence E14 is

    d = W+C(A-2) modulo 4A-5.

Together with C=psi_A(J), d=chi_A(J), and the two strict size
bounds, the chi form of Lemma 2.22 gives

    W=2^J, and therefore b is a power of two.

In particular

    U=N^2w >= Nbw = NW >= 8*2^J > 4*2^(2R).       (3)

Next E13 gives kappa<C, E19 is its Pell equation, and E20 gives
kappa=L modulo A-1. We have 0<L<J<A, the last inequality also
following directly from A=RY(U+1). Lemma 2.23 therefore gives
kappa=psi_A(L), with mu=chi_A(L). By (2) and the initial bounds,

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A.

The congruence E18 and the chi form of Lemma 2.22 consequently give

    q=B^L.

Because B is even by admissibility, q and N=q^16 are now even.
This establishes the parity needed below without using central
binomial divisibility or the final rounding step. The original
Lemma 2.26 is not invoked with a weakened hypothesis: this paragraph
repeats its relevant argument using the independently established
bound A>U^R.

## Round using parity and recover the original stronger bound

The lower bound in (1) gives xi/2<C/K<Y+1, so xi<2Y+2<3Y.
Since M(U+1)<2M^2U, both errors in (1) are less than

    R xi/[M(U+1)] = xi/[Y(U+1)] < 3/(U+1)
      <=3/65<1/4.

Thus |C/K-xi|<1/4. The binomial expansion of Lemma 2.24, using
(3), gives

    0<=xi-floor(xi)<2^(2R)/U<1/4,
    floor(xi) = binom(2R,R) modulo U.

Together with (w), these imply

    |Y-floor(xi)| < 1+1/4+1/4 = 3/2 < 2.

Both integers in this difference are even. Indeed Y=sN^2 and
U=wN^2 are even, while binom(2R,R)=2 binom(2R-1,R-1) is even.
The displayed congruence makes floor(xi) even as well. The only
even integer of absolute value less than 2 is zero, hence

    Y=floor(xi).

It follows that N^2 divides binom(2R,R), as required for the
original no-carry encoding. In fact this also recovers the old
stronger approximation:

    |C/K-Y| <= |C/K-xi|+|xi-floor(xi)| < 1/2.

Therefore eta_strong=K^2-4(C-KY)^2 is a positive integer.
Every solution of the weakened system extends to a solution of the
119-operation system by replacing eta with eta_strong, leaving
all other witnesses unchanged.

Conversely a solution of the old stronger system satisfies the
weakened equation with

    eta_weak=eta_strong+3(C-KY)^2>0.

This proves exact positive-witness equivalence under the admissible
packed encoding. The two algebraic witness maps are

    eta_weak=eta_strong+3(C-KY)^2,
    eta_strong=4 eta_weak-3K^2.

The second map is positive by the proof above; it is not an
unconditional positivity identity. All other changes and their
proofs remain those of the 119-operation alternate-Pell system.

## Accounting and verification boundary

Delete only the instruction f4=4*cm2 and replace the subsequent
comparison by cm2+eta=k^2. All powers and every other operation
remain counted. This gives 67 multiplications and 51 additions,
118 operations in total; the existing 11-step numeral construction
gives 129 if the fixed numerals must be generated from 1.

The companion program checks the changed E10 residual exactly,
retains and rechecks the E7 and E17 triangular identities, and
independently checks every serialized primitive instruction.
Those exact algebraic checks support the count. The positive-domain
equivalence depends on the mathematical parity argument above.
