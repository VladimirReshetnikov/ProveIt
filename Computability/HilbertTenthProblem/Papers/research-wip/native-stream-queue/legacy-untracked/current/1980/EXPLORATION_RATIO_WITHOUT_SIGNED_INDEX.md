# The two norms and positive ratio do not determine the main index

This is a bounded investigation of removing the auxiliary signed-index
block from the 94-operation construction. It gives an explicit alternative
index family for the two main norms, the ratio interval, the first-index
congruence and the first exponential equation. It also satisfies
divisibility of both U and Y by n^2 and the usual coarse bounds on r.
Consequently those conditions alone cannot replace the signed-index
argument. No claim is made that this family satisfies the complete
coefficient encoding or every smaller bound on its packed blocks.
Frozen proofs, certificates and article sources are unchanged.

## 1. Exact family

Let v>=2 be any even integer. Define

    p=v^2+v+1, t=v^2+v/2+1, R=t-1,
    U=4^p, Y=2^v, a=Y(U+1), A=a+4,
    Q=UY^2, P=2Q+1.

Use the positive Pell coordinates

    c=psi_A(p), d=chi_A(p),
    k=psi_P(t), T_Pell=chi_P(t),
    tau=(T_Pell-1)/2.

Because P is odd, T_Pell is odd, and tau is a positive integer.
The two norms hold:

    d^2-(A^2-1)c^2=1,
    tau(tau+1)=Q(Q+1)k^2.

The alternative index difference is

    d_alt=2t-p=v^2+1>1,
    p^2+1=(v^2+1)(v^2+2v+2).

In particular

    (p^2+1)/d_alt-p-1=v.

The actual main index is not the intended one:

    2R+1-p=v^2>0,  p-R=v/2+1>=2.             (1)

## 2. Exact positive ratio interval

Put

    M=(2a)^(p-1)/(4Q)^(t-1).

Since a=Y(U+1), this can be written as

    M=2^(p-2t+1) U^(p-t) Y^(p-2t+1)
      (1+1/U)^(p-1).

Here p-2t+1=-v^2, p-t=v/2, U=2^(2p), and Y=2^v.
The power of two in front has exponent

    -v^2+pv-v^3=v.

Thus the principal ratio is exactly

    M=Y(1+1/U)^(p-1)>Y.                       (2)

The elementary Pell growth bounds used in the existing proofs give

    c/k >= (2A-1)^(p-1)/(2P)^(t-1)
         =M (1+7/(2a))^(p-1)
             /(1+1/(2Q))^(t-1)
         >M.

For the strict final inequality, 7Q>a follows from U,Y>=2, so
7/(2a)>1/(2Q), and p>t. Therefore c/k>Y.

For the upper bound, 2P-1=4Q+1>4Q and the other Pell growth bound give

    c/k < (2A)^(p-1)/(4Q)^(t-1)
         =Y[(1+1/U)(1+4/(Y(U+1)))]^(p-1)
         =Y[1+(Y+4)/(YU)]^(p-1).              (3)

Let z=(Y+4)/(YU) and m=p-1. The explicit values satisfy

    2m(Y+4)<U.                               (4)

Indeed m=v(v+1)<=2^(2v), Y+4<=2^(v+1), and
2m(Y+4)<=2^(3v+2)<2^(2v^2+2v+2)=U for v>=2.
In particular mz<1/(2Y)<1/2. The elementary geometric-series bound
(1+z)^m<=1/(1-mz)<1+2mz now turns (3) into

    c/k < Y+2m(Y+4)/U < Y+1.                  (5)

Combining the strict inequalities gives positive integers

    eta=c-Yk>0, zeta=k-eta>0,

which satisfy exactly c=Yk+eta and k=eta+zeta. This proof uses no
floating-point evaluation or asymptotic remainder assertion.

## 3. First-index and exponential quotients are positive integers

The usual Pell congruence psi_P(t)=t mod(P-1), with P-1=2UY^2,
gives

    h=(k-t)/(UY)=(k-R-1)/(UY)

as an integer. It is positive because t>=2 and psi_P(t)>t. Thus the
retained first-index equation k=R+1+hUY holds with its positive domain.

The first exponential equation also holds, not merely its purported
consequence U=4^p. Let M4=8a+15=A^2-1-a^2. The integer-polynomial
identity for the Pell pair gives

    chi_A(p)-a psi_A(p) == (A-a)^p=4^p=U mod M4.

This follows directly by reducing A^2-1 to a^2 in its even and odd
binomial terms. Hence

    gamma=(d-U-ac)/(8a+15)

is an integer. It is positive: the Pell recurrence gives

    d-ac=4c-psi_A(p-1)>3c,

and c>=A>a>U. Therefore the source equation

    d=U+ac+gamma(8a+15)

has a positive quotient as well. Both norms, both positive interval
equations, the first-index equation, a=Y(U+1) and this exponential
equation are simultaneously satisfied.

## 4. Divisibility and coarse packing bounds do not exclude the family

Take any power of two N>=64 and specialize v=N. Then

    R=N^2+N/2, p=N^2+N+1,
    N^2-1<=R<2N^3, U=2^(2p), Y=2^N.

Since N>=2 log_2 N, both U and Y are positive multiples of N^2.
Thus w=U/N^2 and s=Y/N^2 are positive integers, as required by
the two scale definitions. The bounds U,Y>=N^2, UY>R+1,
A>2R+1 and p>=R+2 also hold. If an eighth-power N is wanted,
take N=2^(8j), with arbitrary j>=1; the same identities apply.

Nevertheless (1) gives p=2R+1-N^2, rather than p=2R+1. Moreover
R=N^2+N/2 has exactly two nonzero binary digits. Therefore

    v_2(binomial(2R,R))=2,

whereas n^2=N^2 requires valuation 2 log_2 N>=12. The divisibility
of Y by N^2 therefore does not by itself imply the desired central
binomial divisibility without the exact main index.

This specialization is not asserted to arise from the full packed
coefficient formulas: those supply additional constraints beyond the
coarse bounds just checked. It is a counterexample to deriving the
index or binomial conclusion from the stated Pell subsystem and
divisibility hypotheses alone.

## 5. Even the unrestricted positive packing identity can be included

For comparison, take a square power of two N>=64, write z=sqrt(N),
and instead choose v=z(N-1). This is even. The same family gives

    R=N(N-1)^2+z(N-1)/2,
    S=N-1-z/2, Tplus=z/2,
    R=S(N^2-N)+Tplus(N^2-1).

Here 0<S,Tplus<N and N^2-1<=R<N^3. Both U and Y are again
multiples of N^2. Thus merely supplementing the Pell subsystem by
the unrestricted positive packing identity does not fix the index
either. In this example S is close to N, so it is not claimed to
meet the sharper bound S<q^7 of the current encoded packing.

A finite search also gives an exact example meeting both sharper
numerical bounds. Take

    q=8, N=q^8=16,777,216,
    v=16,719,975,090,
    R=v^2+v/2=279,557,567,018,580,495,645,
    S=128,193, Tplus=864,995.

Direct integer arithmetic verifies

    R=S(N^2-N)+Tplus(N^2-1),
    0<S,Tplus<q^7=2,097,152,
    N^2-1<=R<2N^3, S=1 mod q^2.

The same parameter-family proof supplies all the stated positive Pell
subsystem witnesses, with both U and Y divisible by N^2. This example
was obtained by solving k(4k+1)=0 mod(N-1), using v=2k, and then testing
the exact quotient and remainder in the packing formula. It shows that
the two smaller numerical block bounds do not alone exclude the family.
It is not a solution of the complete coefficient encoding: no admissible
fixed index, coefficient-code decomposition, geometric equation or
product-offset equation is asserted for these particular S,Tplus,q.

## Conclusion of this bounded search

The alternative-index equation d_alt | p^2+1 has an explicit infinite
family whose leading value of Y is an exact power of two. The tiny
positive shift from A=a+4 supplies the strict ratio interval without
destroying divisibility by N^2. Thus a replacement for the signed-index
block must use additional information, such as the complete encoded
packing structure, or introduce a new independent index restriction.
No certificate reduction is claimed by this note.
