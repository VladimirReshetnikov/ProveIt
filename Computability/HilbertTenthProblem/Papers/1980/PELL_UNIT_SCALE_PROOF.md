# Reusing the interval scale as the Pell scale: an independent 105 operations

This note proves the positive-domain correctness of
`../verification/round18_1980_unit_scale_certificate.py`. It starts from
the 106-operation base-four system in `MAIN_PELL_BASE_FOUR_PROOF.md` and
changes its scale from `M=RY` to `M=Y`. The first Pell index congruence
remains `K=R+1+hQ`. The result has 105 operations: 58 multiplications
and 47 additions, with 34 positive unknowns and 22 equality tests.

This is an independent alternative to the 105-operation index-multiple
system. Its saving does not automatically combine with that system:
here `P-1=2UY^2` is not guaranteed to be divisible by `R+1`.

The fixed admissible encoding index is exactly that of
`MODULAR_SIDON_PROOF.md`, with `L=2^32`. The source Pell facts and the
signed auxiliary block are those already cited in
`MAIN_PELL_BASE_FOUR_PROOF.md` and `PELL_SIGNED_PROOF.md`. The following
argument supplies the changed size, approximation, and necessity proofs;
the companion checker supplies the exact arithmetic identities.

## Equations and the previously unused upper bound on the packed index

Write

    N=n, R=r, U=w*N^2, Y=s*N^2,
    M=Y, a0=Y*(U+1), A=a0+4,
    Q=U*Y^2, P=2Q+1, J=2R+1, K=k, C=c, W=bw.

The supplied positive coordinate called `a` is still `a0`; every main
Pell expression still uses the mathematical parameter `A=a0+4`.
Retain

    tau*(tau+1)=Q*(Q+1)*K^2,
    K=R+1+hQ,
    C=KY+eta, K=eta+zeta, eta,zeta>0.             (1)

Replace the defining equation for `a0` by

    a0=Y*(U+1).                                 (2)

All other equations, including both exponent congruences and the signed
block, are unchanged. Only E9, E11, and E12 have changed expanded
polynomials, through Q and a0.

The coding bootstrap is independent of all these changes. Before either
exponential relation is known, it proves

    N=q^8, q>4b>=8, 3L<=B<=N<=R, b<=N, q<=N,
    0<S<N, 0<=T<N,
    R=S(N^2-N)+(T+1)(N^2-1).

In particular, integrality of S,T gives the additional upper bound

    R <= (N-1)(N^2-N)+N(N^2-1)
       =2N^3-2N^2 < 2N^3.                      (3)

Thus `N,R>=64`, `U,Y>=N^2>=4096`, and

    a0=Y(U+1)>N^4>4N^3+1>J,
    Q=UY^2>=N^6>2N^3+1>R+1.                    (4)

These are noncircular bounds: they use only positivity, the geometric
equation, and the already proved ranges of the packed blocks. In
particular, neither b nor q is assumed to be a power of two here.

## Recovering both Pell indices

Equation (1) gives `K>=R+2`, so its positive interval gives
`C>YK>=4096(R+2)>J`. The signed auxiliary block therefore applies
with parameter A and proves

    C=psi_A(J), d=chi_A(J).                       (5)

The triangular norm in (1), with `T_Pell=2tau+1`, gives

    T_Pell^2-(P^2-1)K^2=1.

Consequently `K=psi_P(t)` for a positive index t. The congruence of
the Pell sequence modulo `P-1=2Q`, and hence modulo Q, gives

    t=R+1+vQ, v>=0,

where (4) justifies the nonnegative representative. If v is positive,
elementary Pell growth and `Q>=R` give

    C/K <= (2A)^(2R)/(2P-1)^(R+Q)
         <= (2A/(2P-1))^(2R) < 1/2.

The last inequality follows from

    (2P-1)-4A=4Y[U(Y-1)-1]-15>0,

using `U,Y>=4096`. It contradicts `C/K>Y`. Thus

    K=psi_P(R+1), T_Pell=chi_P(R+1).             (6)

The proof has not used an exponential relation or binomial rounding.

## Ratio bounds with the smaller scale

Put `xi=(U+1)^(2R)/U^R`. Since M still cancels from the principal
ratio, the exact indices (5)--(6) give

    C/K >= xi*(1+7/(2a0))^(2R)*(1+1/(2Q))^(-R)
         > xi.                                  (7)

Indeed `(1+7/(2a0))^2>1+7/a0>1+1/(2Q)` because
`14Q>a0`, which follows from `Q=UY^2`, `a0=Y(U+1)` and `U,Y>=4096`.

For the upper bound, Pell growth gives

    C/K < xi*(1+4/a0)^(2R).

The packed-index bound (3) now replaces the old factor R in M:

    8R/a0 < 16N^3/N^4=16/N<=1/4<1/2.

For `m=2R` and `t=4/a0`, the elementary inequality
`(1+t)^m<=1/(1-mt)<1+2mt` therefore gives

    C/K < xi*(1+16R/a0).                        (8)

The positive interval and (7) imply `xi<Y+1`. Since `xi>U^R`
and Y is an integer, this proves

    Y>=U^R, a0=Y(U+1)>U^(R+1), A>a0.            (9)

This bound is established before exponent decoding. Also
`xi<Y+1<2Y`, so (8) gives

    0<C/K-xi<32R/(U+1).                         (10)

At this stage the right side is not asserted to be less than one.
The exponential relation proved next supplies that stronger estimate.

## Decode the exponents before using the small error

Since `W=bw<=U`, `N>=64`, `U>=4096`, and (9) holds,

    4^(3J)=64*64^(2R)<=64*N^(2R)
           <=64*U^R<U^(R+1)<A,
    W^3<=U^3<=U^R<A.

The unchanged base-four chi congruence

    d=W+C(A-4)+gamma(8A-17)

therefore proves `W=4^J` by the source exponent lemma. In particular
b is a power of two, and

    U=N^2w>=Nbw=N4^J>=64*4^J>64R.              (11)

Here `4^(2R+1)>R` holds for every positive integer R. Combining
(10) with (11) now gives the required small error

    0<C/K-xi<1/2.                               (12)

The positive gap `0<kappa<C`, its Pell norm, and
`kappa=L modulo(A-1)` identify `kappa=psi_A(L)` and `mu=chi_A(L)`:
the hypotheses `0<L<J<A` follow from (4) and `3L<=B<=N<=R`.
Furthermore,

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A.

The unchanged second exponent congruence therefore gives `q=B^L`.

By (11), `U>=N4^J>4*2^(2R)`. The binomial expansion of xi has
integer part F satisfying

    0<xi-F<2^(2R)/U<1/4,
    F=binom(2R,R) modulo U.

Now (7), (12), and the interval imply

    F<xi<C/K<Y+1,
    Y<C/K<xi+1/2<F+3/4.

Integrality forces `Y=F`, and thus `N^2` divides `binom(2R,R)`.
The established power-of-two and no-carry conclusions therefore feed
into the unchanged homogeneous modular-Sidon decoding. This proves
sufficiency for exactly the same represented set and fixed index.

## Necessity with all positive witnesses

Given a solution of the represented system, choose the canonical coding
witnesses from `MODULAR_SIDON_PROOF.md` and the base-four proof. They
determine b,B,q,N,R before the Pell witnesses are chosen. They satisfy
the bounds used above, including (3), and `N^2` divides `binom(2R,R)`.
Choose

    J=2R+1, w=4^J/b, U=N^2w,
    Y=floor((U+1)^(2R)/U^R), s=Y/N^2,
    a0=Y(U+1), A=a0+4, Q=UY^2, P=2Q+1,
    C=psi_A(J), d=chi_A(J), K=psi_P(R+1).

As in the base-four proof, b is a power of two and `b<=R`, so w is a
positive integer. The binomial expansion and the central-binomial
divisibility make s a positive integer. In particular `Y>=N^2`, so
all purely numerical hypotheses of (7)--(8) hold for these choices.
Here `xi<Y+1` holds by the definition of Y, and (11) holds directly
from the chosen w. Thus the same error estimate (12) gives

    Y<xi<C/K<xi+1/2<Y+3/4.

The values `eta=C-KY` and `zeta=K-eta` are positive integers. Put

    tau=(chi_P(R+1)-1)/2, h=(K-R-1)/Q.

The first is positive integral because P is odd and its chi sequence
is odd. The second is integral by the Pell congruence modulo `2Q`
and positive by strict growth `psi_P(R+1)>R+1`. These choices give
exactly (1)--(2).

Choose the remaining Pell witnesses by their generic constructions
at the new A: positive f,i with `f^2-(A^2-1)(iC^2)^2=1`, then

    G=1+(A+1)(f^2-1), I=chi_G(J), H17=psi_G(J),
    o=(I+d)/f, j=(H17-J)/C.

The same congruences `G=-A modulo f`, `G=1 modulo C`, and odd J
make o and j positive integers and give `of-d=I`.
Choose `kappa=psi_A(L)`, `mu=chi_A(L)`,
`Delta=(kappa-L)/(A-1)`, and `phi=C-kappa`. Their positivity and
integrality follow from `2<=L<J` and the Pell congruence and growth.

The exponent lemma supplies integral gamma and rho, and their
positivity follows from

    d-(A-4)C=4C-psi_A(J-1)>3C>4^J,
    mu-(A-B)kappa=B*kappa-psi_A(L-1)>(B-1)kappa>B^L.

The last inequalities use the bounds `A>W^3`, `A>q^3` established
from (9), and `J,L>=2`. Both moduli are positive since `A>B`
and `A>4`. All positive coding witnesses, including Omega and sigma,
are unchanged. Thus every altered coordinate is explicitly chosen;
the proof does not assert preservation of the old value of a0.

## Exact arithmetic saving

The predecessor calculates `Y=s*N^2`, then spends one multiplication
on `M=R*Y`. Delete that multiplication and reuse the existing Y
register everywhere M was used. In particular,

    UM=U*Y, a0=UM+Y, Q=UM*Y

use exactly the same three instructions as before. The index equation
`K=R+1+hQ` is retained, including both of its arithmetic operations.
The complete count decreases from 106 to 105 by one multiplication.

The checker verifies every expanded source residual, both inherited
triangular corrections, the updated meanings of Q and a0, all declared
input uses, and every serialized addition or multiplication. It checks
that exactly E9, E11 and E12 changed, and records the unchanged fixed
support inequalities and the new operation histogram in its JSON.
