# Forcing the Pell index to be a positive multiple: 105 operations

This note proves the positive-domain correctness of
`../verification/round16_1980_index_multiple_certificate.py`, a successor
to the 106-operation base-four construction in
`MAIN_PELL_BASE_FOUR_PROOF.md`. The fixed encoding and all its parameters
are unchanged. The construction saves one addition by changing both the
definition of an intermediate scale and the first Pell index equation.

The elementary Pell lemmas are those in the corrected source
`../1982/jones1982_corrected.tex`; the signed Pell block is the separately
proved construction in `PELL_SIGNED_PROOF.md`. No new Lean theorem is
asserted. The companion checker verifies every primitive instruction and
every source residual identity; the following proof establishes the
changed index argument and positive witness construction.

## Changed scale and index equation

Use the notation

    N=n, R=r, U=w*N^2, Y=s*N^2,
    D=R+1, M=D*Y, a0=M*(U+1), A=a0+4,
    Q=U*M^2, P=2Q+1, J=2R+1, K=k, C=c.

Here `a0` remains the supplied positive unknown named `a` in the
checker. Replace the previous definition `M=R*Y` by `M=(R+1)*Y`.
Replace the previous equation `K=R+1+hQ` by

    K=h*(R+1)=hD.                               (1)

The unknown `h` is still a positive integer. Retain the norm and interval

    tau*(tau+1)=Q*(Q+1)*K^2,
    C=KY+eta, K=eta+zeta, eta,zeta>0.             (2)

All remaining source equations are unchanged as polynomials in the
supplied unknowns. In particular, the main Pell parameter is still
`A=a0+4`; the signed block still tests `C=psi_A(2R+1)`; and the exponent
congruences still use bases 4 and B. Because M occurs through the
calculated values Q and a0, precisely E9, E11 and E12 acquire different
expanded source polynomials.

## Exact index before either exponential relation

The unchanged coding bootstrap establishes

    N=q^8, q>4b>=8, 3L<=B<=N<=R, b<=N, q<=N.

Thus `N,R>=64`, `U,Y>=4096`, and the new value `M=(R+1)Y` satisfies
every earlier lower bound on `RY`, including `M>=262144`.
Equation (1) gives `K>=R+1`. The positive interval therefore gives

    C>YK>=Y(R+1)>2R+1=J.

The hypotheses of the generic signed Pell argument hold with main
parameter A, yielding

    C=psi_A(J), d=chi_A(J).                       (3)

Set `T=2tau+1`. The norm in (2) is exactly

    T^2-(P^2-1)*K^2=1, T>1.

Consequently `K=psi_P(t)` and `T=chi_P(t)` for a positive integer t.
The key new divisibility is

    P-1=2Q=2U(R+1)^2Y^2,

which is divisible by D. The elementary Pell congruence
`psi_P(t)=t modulo(P-1)` therefore implies `K=t modulo D`.
Equation (1) makes K a multiple of D, so

    t=mD=m(R+1), m>=1.                          (4)

If `m>=2`, then `t-1>=2R+1`. The elementary growth bounds give

    C/K <= (2A)^(2R)/(2P-1)^(2R+1)
         < (2A/(2P-1))^(2R) < 1/2.              (5)

For completeness, the shifted main parameter still satisfies
`2A/(2P-1)<1/2`. This is equivalent to

    4UM(M-1)-4M-15
      =4M[U(M-1)-1]-15 > 0,

which follows already from `U>=64` and `M>=512`. Inequality (5)
contradicts `C/K>Y`. Thus m=1 and

    K=psi_P(R+1), T=chi_P(R+1).                  (6)

This argument uses only the initial coding bounds, the positive
interval, the signed Pell block, and the new norm and index equations.
It assumes neither exponential decoding nor binomial rounding. No
parity restriction on the quotient h is needed.

## The ratio estimate is preserved

Put `xi=(U+1)^(2R)/U^R`. At the two exact indices (3) and (6), M still
cancels from the principal ratio because

    (2M(U+1))^(2R)/(4UM^2)^R=xi.

The same growth estimates, with the new M, consequently give

    C/K >= xi*(1+7/(2a0))^(2R)*(1+1/(2Q))^(-R)
         > xi,                                 (7)

and

    C/K < xi*(1+4/a0)^(2R)
         < xi*(1+16R/a0)
         < xi*(1+16/[Y(U+1)]).                  (8)

The lower bound uses `14Q>a0`, valid for `Q=UM^2`,
`a0=M(U+1)`, `M>=2` and `U>=1`. For the upper bound, set
`t=4/a0`, `m=2R`; then

    mt=8R/[(R+1)Y(U+1)] < 8/[Y(U+1)] < 1/2.

The elementary estimate `(1+t)^m<=1/(1-mt)<1+2mt` proves the
middle inequality. The final inequality in (8), formerly an equality
at this point of the estimate, follows from `R/(R+1)<1`.

The positive interval and (7) give `xi<Y+1`. Since `xi>U^R` and Y is
an integer, `Y>=U^R`. Therefore

    a0=(R+1)Y(U+1)>R U^R, A>a0.                (9)

Also `xi<Y+1<2Y`, so (8) gives the same strict error bound

    0<C/K-xi<32/(U+1)<1/2.                     (10)

Thus the changed scale preserves, and slightly strengthens, every
ratio and size inequality needed by the base-four construction.

## Exponents, rounding, and encoding soundness

For clarity, the complete remaining chain of implications is as follows.
Let `W=bw`. Since `W<=U`, `N,R>=64`, and (9) holds,

    4^(3J)=64*64^(2R)<=64*N^(2R)<=R U^R<A,
    W^3<=U^R<A.

The unchanged base-four chi congruence gives `W=4^J`. In particular
b is a power of two, and `U>=NW=N4^J>4*2^(2R)`.

The positive gap `C>kappa`, its Pell norm and
`kappa=L modulo(A-1)` imply `kappa=psi_A(L)` and
`mu=chi_A(L)`, since `0<L<J<A`. The same size comparisons give

    B^(3L)<=B^B<=N^N<=U^R<A,
    q^3<=N^N<=U^R<A.

The second chi congruence gives `q=B^L`. The binomial expansion has
integral part F with

    0<xi-F<1/4, F=binom(2R,R) modulo U.

Now `F<xi<C/K<Y+1` and
`Y<C/K<xi+1/2<F+3/4` force `Y=F` by integrality. Hence
`N^2` divides `binom(2R,R)`. With b, B, q and N powers of two,
the unchanged no-carry and modular-Sidon decoding recovers the original
represented system. This proves sufficiency without reusing an index
congruence that is no longer present.

## Necessity and positive witnesses

Start with a solution of the represented system. Choose the canonical
coding witnesses exactly as in `MAIN_PELL_BASE_FOUR_PROOF.md` and
`MODULAR_SIDON_PROOF.md`. They determine b, B, q, N and the packed R
before any Pell witnesses are chosen, with b a power of two,
`R>=N>=64`, and `N^2` dividing `binom(2R,R)`.

Set

    J=2R+1, w=4^J/b, U=N^2*w,
    Y=floor((U+1)^(2R)/U^R), s=Y/N^2,
    M=(R+1)Y, a0=M(U+1), A=a0+4,
    Q=UM^2, P=2Q+1,
    C=psi_A(J), d=chi_A(J), K=psi_P(R+1).

The base-four proof establishes that w is positive integral and that
the binomial expansion makes s positive integral. These assertions
depend on R,U,N and the coding witnesses, not on the changed M.
Estimates (7)--(8) hold at these chosen indices. Since Y is now
defined as the floor of xi, (10) holds directly. They imply

    Y<xi<C/K<xi+1/2<Y+3/4.

Thus `eta=C-KY` and `zeta=K-eta` are positive integers. Choose

    tau=(chi_P(R+1)-1)/2,
    h=K/(R+1).

The parameter P is odd, so its chi recurrence gives an odd value
greater than one and tau is positive integral. The congruence
`psi_P(R+1)=R+1 modulo(P-1)`, together with `R+1` dividing P-1,
shows that K is divisible by R+1. Therefore h is a positive integer
and satisfies exactly the new equation (1). This quotient is a
chosen positive unknown, not an uncharged division instruction.

Choose the remaining dependent Pell witnesses using their same generic
constructions at the new A. In detail, choose positive f,i satisfying
`f^2-(A^2-1)(iC^2)^2=1`, and put

    G=1+(A+1)(f^2-1), I=chi_G(J), H17=psi_G(J),
    o=(I+d)/f, j=(H17-J)/C.

As in `PELL_SIGNED_PROOF.md`, `G=-A modulo f`, `G=1 modulo C`,
and odd J make o and j positive integers; they give `of-d=I`.
Set `kappa=psi_A(L)`, `mu=chi_A(L)`,
`Delta=(kappa-L)/(A-1)`, and `phi=C-kappa`. The congruence and
`2<=L<J` make Delta and phi positive integers.

The two exponent congruences yield integral gamma and rho. Their
positivity follows exactly as before from

    d-(A-4)C>3C>4^J,
    mu-(A-B)kappa>(B-1)kappa>B^L,

using `A>W^3`, `A>q^3`, and the positivity of both moduli.
Those strict size bounds follow from (9), which holds here because
`Y>=U^R`. All coding witnesses, including positive Omega and sigma,
are unchanged. This constructs every new positive witness and proves
necessity. In particular, M and every dependent Pell coordinate are
recomputed; the proof does not identify the old and new values of h.

## Exactly one arithmetic operation disappears

The predecessor already computes `r1=r+1` for its signed-block index
`J=r1+r`. Move that existing instruction before the calculation of M.
Replace `M=rY` by `M=r1*Y`; its cost remains one multiplication.
Replace the old multiplication `hQ` by `h*r1`, and replace the old
free equality `k=r1+hQ` by `k=h*r1`. The addition `r1+hQ` disappears.

All other arithmetic instructions keep their previous count. The
result is exactly 105 operations: 59 multiplications and 46 additions,
with the same 34 positive unknowns and 22 equality tests. The inherited
nine-operation numeral chain gives a complete 114-operation certificate
using only literal 1; this is not claimed to improve the separate
strict-count milestone.

The checker verifies the changed source equations E9, E11 and E12,
checks that every other source polynomial is identical to its
predecessor, and verifies both triangular residual corrections.
It also verifies the full primitive core and strict schedules and
records the changed meanings of M, Q and h explicitly in the JSON.
