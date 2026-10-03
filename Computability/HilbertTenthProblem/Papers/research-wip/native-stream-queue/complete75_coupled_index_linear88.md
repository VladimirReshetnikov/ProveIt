# Coupled index and linear units give an 88-operation universal polynomial

> The [asymmetric-scale successor](complete75_asymmetric_scale_tradeoffs.md)
> retains the87/88 operation counts and19 witnesses while lowering their
> exact degrees to169/125. Each successor has a full positive-zero bijection
> to its respective parent. The source and degree analysis below remain
> the reproducible historical construction.

For every computably enumerable set of positive integers, the fixed
complete75 compiler now gives a single integer polynomial evaluated by
**88=47 multiplications+41 additions/subtractions**, with **19 strictly
positive existential witnesses** and the ordinary input x. Its exact
total degree is **151**. The comparison certificate costs 87 operations
and has one equation. The separate best comparison bound remains 75.

One subtraction is saved by sharing k-hE between the index and linear
unit factors of [positive-root89](complete75_positive_root89.md).
This coupling leaves a second possible index sign that the earlier local
Pell argument alone cannot exclude. The fixed compiler masks exclude it:
the displaced packed index has at most 3t+1 bits, whereas its recovered
Pell kernel requires at least 3t+2. The complete strong auxiliary square,
both positive ratio slacks and all ordinary-input constraints remain.

Under the fixed compiler hypotheses below, this polynomial and
positive-root89 have **identical positive solution sets on the same
nineteen coordinates**. They are not identical polynomials. The previous
89-operation degree 148 result remains a distinct cost/degree tradeoff.

## 1. Fixed hypotheses, coordinates and factors

Use precisely the constants of the [complete75 compiler](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md).
In particular, the part of its mask contract needed for the new argument is

    B=2^d, d>=4, 0<MC,MF<B-1,
    MC=2 modulo 4, MF=4 modulo 8,
    popcount(MC)+popcount(MF)=d.                       (1)

All remaining compiler constants, synchronization layout and input
conventions are retained. Positive zero-set equivalence is asserted
under this contract; it is not asserted for arbitrary numerical masks
satisfying only size inequalities.

The supplied positive coordinates are

    J,F,alpha,zplus,f,h,i,j,o,s,w,g,eta,zeta,y,Z,delta,rho,sigma,

with source names Jrep,tau_gap,y_aux for J,g,y. Alongside x>0, compute the
same definitions as positive-root89:

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    A=a+2, Delta=A^2-1, H=4a+3,
    D=X+ac+(rho+sigma)H,
    C=q-F-Z-alpha-2d*x, W=C-Z,
    kappa=2d*x+b+delta*Delta, mu=W+a*kappa+rho*H,
    G=q^2-Z-qF,
    R=G*(q^2-1)+(MC+q*(MF+B-1))*J,
    T=i*c^2, K=Delta*(f^2-1), V=of-c.                  (2)

These are computed expressions, not extra supplied coordinates; they
may be signed away from zeros. Put K0=DC+B*DR, also a fixed numeral.
The eight factors of the new polynomial are

    N0=g^2+E*(kY)*(2g-k),
    N1=D^2-Delta*c^2,
    N2=mu^2-Delta*kappa^2,
    N3=K*(V^2-y^2)+y^2,
    Nk=k-R-hE,
    Nt=(K0+X)C+(q-F)-zplus*(q-1),
    N4=1+T^2-K,
    Lnew=V-jc+k-hE.                                  (3)

The polynomial is the unsquared expression

    N0*N1*N2*N3*Nk*Nt*N4*Lnew-1.                     (4)

Its ordinary integer zero set is used with the declared positive domain.
There are no extra comparisons or uncharged residual tests.

## 2. The five norm factors are positive units at every zero

At a zero of(4), all eight integer factors are units, hence each is 1 or -1.
The sign arguments for the first seven factors are unchanged from the
preceding 89 source; they require no equation about Lnew.

For clarity, Delta is 0 or 3 modulo 4, so the norm expressions N1,N2 can
never be -1 modulo 4, even for signed roots. Also K is 0 or 1 modulo 4,
because K=(A^2-1)(f^2-1). Thus N3 is congruent to y^2 or V^2, and
N4=1+T^2-K is 0, 1 or 2 modulo 4. Consequently

    N1=N2=N3=N4=1, K=T^2.                            (5)

For N0 put V0=XY^2>1 and reconstruct the positive root
`tau=V0*k+g`. The exact positive-root identity gives

    N0=tau^2-V0*(V0+1)*k^2.

The negative Pell equation at V0(V0+1) has no integer solution when
V0>1. An elementary descent proves this: for a supposed solution
x^2-V0(V0+1)z^2=-1 with x,z positive and z minimal, the integer
`z'=(2V0+1)z-2x` satisfies 0<z'<z, since
`V0*z<x<(V0+1/2)z`. Multiplication by the inverse unit
`2V0+1-2*sqrt(V0(V0+1))` gives another negative-norm integer solution
with coefficient z', contradicting minimality. Zero coordinates cannot
solve the equation, and signed coordinates can first be replaced by
absolute values. Hence N0=1 as well.

Write

    Nk=epsilon, Lnew=lambda, Nt=nu,
    epsilon,lambda,nu in {1,-1}, epsilon*lambda*nu=1.  (6)

No sign for these three factors is assumed prematurely.

## 3. Outer positivity and the displaced auxiliary target

Weak transport Nt in {1,-1} implies C>=0. Indeed F>=1 and zplus>=1 give
`q-F-zplus*(q-1)<=0`; if C<=-1 then Nt<=-(K0+X)<-1. Since alpha and
2d*x are positive, the definition of C gives F+Z<q. In particular,

    2q-1<=G<=q^2-q-1.

The mask inequalities in(1) give
`0<(MC+q*(MF+B-1))*J<(q-1)(1+2q)`. Therefore

    (2q-1)(q^2-1)<R<q^4-q^3,
    3q+1<R-2<R+2<q^4,
    E>=q^6>2(R+2), a>R+2.                            (7)

All of this precedes any conclusion that q is a power of two. Notice
that the stronger lower bound leaves room for shifting R down by two.

The index factor gives k=R+epsilon+hE. Since h>=1,
`k>R+2` and c>kY>2(R+2). Set P=2XY^2+1. The first norm's elementary
Pell classification gives n>=1 with

    tau=chi_P(n), k=2*psi_P(n).

As P=1 modulo E, the index equation gives

    2n=R+epsilon modulo E,
    n>=(R-1)/2>=24.                                  (8)

The positive main root D and N1=1 give
`c=psi_A(p), D=chi_A(p)` for p>=1. Since P>A and c>k, monotonicity gives
p>=n+1>=25. In particular,

    c>A*Delta^2, c>2p, c>2(R+2).                     (9)

For the first inequality use
`c>(2A-1)^(p-1)>A^5>A*(A^2-1)^2`, as in the retained kernel.

The [generic strong-rank theorem](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md)
now applies to T^2=Delta*(f^2-1), with T=ic^2, giving

    f=chi_A(m), c divides m, m>=c>2p,
    T=Delta*psi_A(m).

It follows that f>chi_A(2p)=1+2Delta*c^2>2c, and therefore V=of-c>0.
Neither the linear unit nor input exponent decoding was used in this step.

Define the temporary index target

    Jtarget=R+epsilon-lambda, in{R-2,R,R+2}.           (10)

The exact identity Lnew=lambda, together with Nk=epsilon, is

    V=jc-Jtarget.

At the same time V=of-c. The size bounds give
`0<Jtarget<c/2` and `0<p<c/2`. Apply the signed-index argument from
[the reversed auxiliary packet, Section4](complete75_reversed_auxiliary89.md)
with this target. Its hypotheses are exactly the positive auxiliary root
V, the strong rank m>=c>2p, and these two strict target bounds. It yields

    p=Jtarget=R+epsilon-lambda.                       (11)

More explicitly, N3=1 and K=T^2 classify TV,y by an odd Pell index ell
at parameter T. The odd-index polynomial gives
`V=(-1)^v*psi_A(ell) mod f` and `V=(-1)^v*ell mod c` for ell=2v+1.
The congruence V=-c mod f and signed chi step-down yield ell=+p or-p
modulo m, hence modulo c. The congruence V=-Jtarget mod c then gives
Jtarget=+p or-p modulo c. Bounds(9),(10) exclude the negative alternative
and all nonzero multiples of c, proving(11). This uses the generic
step-down proof, not the whole kernel with an index equation assumed
in advance.

## 4. The ratio removes one sign and identifies a complete kernel

Since n<p<=R+2 and E>2(R+2), both representatives in(8) lie strictly
between 0 and E. Thus

    2n=R+epsilon, p-2n=-lambda.                      (12)

If lambda=-1, then p=2n+1. For Q=chi_A(2)=2A^2-1 one has Q>P and
A>Y+1. Pell duplication and monotonicity imply

    psi_A(2n)=2A*psi_Q(n)>=2A*psi_P(n)=A*k.

Hence c=psi_A(2n+1)>A*k>k(Y+1), contrary to the strict ratio
`kY<c<k(Y+1)` supplied by eta,zeta>0. Consequently

    lambda=1, nu=epsilon,
    p=R+epsilon-1, k=p+1+hE, V=jc-p.                 (13)

At this point **all ten equations of the original
[half-binomial42 kernel](pell_kernel_half_binomial42.md) hold with its
index set to p**. The first root is the reconstructed positive tau;
its main root is D; the main gamma is rho+sigma; the auxiliary root is
V=jc-p=of-c; and the actual strong square T^2=(ic^2)^2 remains. All
required supplied kernel coordinates are positive, including both ratio
slacks. Bounds(7) give its external range3q+1<=p<q^4 at both signs.
It therefore proves

    X=2^p, q=2^t, p=3 modulo 4,
    popcount(p)>=3t+2.                               (14)

No input-norm decoding is needed to invoke this kernel. The remaining
sign is resolved next, rather than assumed to follow from the ratio.

## 5. The compiler masks exclude the remaining negative sign

Since q=(B-1)J+1 and B=2^d, the conclusion q=2^t implies d divides t.
Write q=B^N with N>=1 and J=1+B+...+B^(N-1); then t=dN.
Set Lambda=q^2 and S'=Z+qF-1. Positivity and F+Z<q give
`0<S'<Lambda`. The exact shifted packing identity is

    R=(Lambda-S')*(Lambda-1)+T',
    T'=MC*J+1+q*(MF*J-1).                            (15)

Suppose epsilon=-1. Then p=R-2, and(15) becomes

    p=(Lambda-S')*(Lambda-1)+Tminus,
    Tminus=(MC*J-1)+q*(MF*J-1).                       (16)

The inequalities in(1) ensure 0<Tminus<Lambda-1. The mask words are
repeated in disjoint base-B cells, so

    popcount(MC*J)+popcount(MF*J)=dN=t.

Moreover J is odd, v2(MC*J)=1 and v2(MF*J)=2. Subtracting one therefore
leaves the low mask's population unchanged and increases the high
mask's population by one. The two blocks of(16) occupy disjoint groups of t binary positions:
each coefficient is smaller than q=2^t. Thus

    popcount(Tminus)=t+1.                            (17)

The [inverse-packing bound used in the complete75 proof, Section3](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
applies to(16), because 0<S'<Lambda and0<Tminus<Lambda-1. It gives

    popcount(p)<=2t+popcount(Tminus)=3t+1,             (18)

contradicting(14). Therefore epsilon=1. By(13), nu=lambda=1 as well.
This argument specifically uses the compiler masks in(1); ignoring
those masks would leave the negative index/transport branch open.

The missing bit in(18) is exact. For example S'=4q (F=4,Z=1) is disjoint
from Tminus because MF*J-1 is 3 modulo 8, and attains the inverse-packing
maximum 3t+1. These are packing-only fixtures, not complete source zeros.

## 6. Complete equivalence and the one-operation saving

Write the preceding linear unit as

    Lold=1+V-(jc-R).

The exact polynomial identity is

    Lnew=Lold+Nk-1.                                  (19)

We have proved at every positive zero of(4), under(1), that all eight
new factors equal 1. Then Nk=1 and(19) give Lold=1. Every factor of
positive-root89 is therefore1 on the same supplied tuple. Its complete
ordinary-input theorem restores the positive old quotient zplus-1 and
all other eliminated positive witnesses, establishing soundness here.
Conversely every positive zero of positive-root89 has all eight old
factors equal 1. Equation(19) gives Lnew=1 on that identical tuple, so
(4) vanishes. Canonical compiler completeness is consequently inherited
without modifying its fixed numerals, input map or witness domains.

The [checker](complete75_coupled_index_linear88.py) makes four gate changes
and deletes one gate from the actual 89 source. Both hE and jc retain
their paid multiplications:

| Old five additions/subtractions | New four additions/subtractions |
|---|---|
| `index_difference=k-R` | `index_difference=k-hE` |
| `Nk=index_difference-hE` | `Nk=index_difference-R` |
| `U=jc-R` | deleted |
| `linear_difference=V-U` | `linear_difference=V-jc` |
| `Lold=linear_difference+1` | `Lnew=linear_difference+index_difference` |

Every other gate is identical; the circuit is reordered topologically.
There is no paid evaluation of Lold or U in the new polynomial. They are
proof abbreviations only. The resulting literal ledger is

    certificate:87=47M+40A, one equation product=1;
    polynomial: 88=47M+41A, output product-1.         (20)

Every multiplication by a fixed numeral, every square and each binary
addition or subtraction is charged. The [receipt](complete75_coupled_index_linear88.json)
contains the full polynomial DAG, witness list and sole comparison.

## 7. Exact degree and verification

Give x and all nineteen supplied witnesses degree one, and fixed
numerals degree zero. Write Q=(B-1)J, k0=eta+zeta,
gamma0=rho+sigma and Ctop=Q-F-Z-alpha-2d*x.
The old linear unit had degree 6. Here Lnew has degree 9 with highest form
`-h*w*s*Q^6`, the same highest form as Nk. The eight factor degrees are

    14,22,42,28,9,5,22,9,

whose sum is 151. Multiplying their highest forms gives

    -32*(B-1)^99*h^2*(rho+sigma)*delta^2*i^2*f^2
      *(eta+zeta)^8*w^13*s^20*J^99
      *Ctop*(2g-eta-zeta).                           (21)

It is nonzero for all admissible fixed B: Ctop and the final linear
factor have nonzero F and g coefficients. Thus the exact degree is 151.
This higher degree explains retaining the89/148 construction.

Default execution recomputes the deterministic receipt:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_coupled_index_linear88.py

The checker audits all gate dependencies, the four changed instructions,
the single deleted subtraction, unchanged comparison and exact counts.
On 512 assignments (384 positive and128 signed supplied assignments), it
checks every new factor and the full polynomial against the original
nineteen source residuals after reconstruction. The last corrected factor
is `1+r8-r14`. Independently it verifies the exact parent correction

    polynomial88=polynomial89+seven_units*(Nk-1).

Those fixtures include four deliberately negative computed input roots;
they establish algebraic identities, not accepting compiler tuples.
Three weighted, offset univariate specializations check all factor
degrees, the degree 151 output and the explicit leading coefficient(21).
The coupled-unit identity is checked symbolically. Additional tests
cover all four sign combinations, exact Pell duplication/ratio comparisons,
compiler-mask repetitions and the displaced inverse-packing population
bound, including the sharp missing-one-bit fixtures above. These finite
audits supplement the parametric proof; they do not replace it.

No deletion of a ratio inequality or strong norm is implicit in this
saving. The conclusion is for positive integer witnesses and the full
compiler contract, with the original ordinary positive input. No global
operation optimum, real-witness equivalence or proof-assistant
formalization is claimed.

Two independent full proof/source/default reviews passed without findings.
They checked the unconditional norm signs, weak positivity and all three
displaced target bounds before decoding; the generic strong-rank recovery;
the exact ten-equation kernel at p; and the compiler-specific missing-bit
contradiction. One independently checked 512 direct eight-factor identities,
including 6 negative computed input roots and 189 zero restored quotients,
and an additional B=128,d=7 weighted/offset degree 151 leading-form audit.
The other verified 8,192 additional source-packing cases at d=8 through 20
and 256 sharp displaced fixtures. Both confirmed the literal 88 ledger
and identical positive solution sets under the stated compiler contract.
