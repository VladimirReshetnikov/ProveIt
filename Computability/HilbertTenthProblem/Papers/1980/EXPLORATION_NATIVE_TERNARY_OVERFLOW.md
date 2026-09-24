# Native ternary overflow rejection and a complete four-field interface

This note extends the conditional native-positive ternary component without
changing its frozen proof or checker. It proves a sharp carry rejection
interval, the larger preliminary bounds needed before decoding, and a
complete 60-operation relation on four positive packed fields. A counter
seed, program control, raw numerical input, and a halting construction are
not part of that relation. No improved universal bound is claimed.

The existing component is `EXPLORATION_BASE_THREE_POSITIVE_KERNEL.md`.
The new exact arithmetic and finite checks are in
`../verification/explore_native_ternary_overflow.py` and its JSON receipt.
The separate counter-ripple application is owned by
`EXPLORATION_NATIVE_TERNARY_RIPPLE.md`.

## 1. The sharp extended mask

Let N>=1, L=3^N, and

    Jbig=(L-1)/2, D0=3L, r=3P0+2.

For every integer 0<=P0<L+Jbig,

    D0 | binom(2r,r)
      iff P0<L and all N ternary digits of P0 are 1 or 2. (1)

The digits include leading positions. For P0<L this is the native mask
theorem: r has initial digit 2 followed by the N digits of P0. Its N+1
possible carries are all present exactly when those N digits are positive.

Now let P0=L+x, with 0<=x<Jbig. Compare the N digits of x with the
all-one ternary word Jbig. At the highest position where they differ,
x has digit zero, and every higher position has digit one. This follows
from ordinary lexicographic comparison of equal-length radix expansions;
the lower digits of x can have any values.

The digits of r are the initial 2, the N digits of x, and an extra top
digit one. The identified zero digit emits no carry when r is doubled,
regardless of its incoming carry. Every higher digit is one, so no carry
restarts there: 1+1=2<3. The extra top one also emits no carry. At least
two of the N+2 positions therefore lack carries. Above the extra top
position no carry can be generated. Kummer's theorem gives

    v_3(binom(2r,r))<=N<N+1,

and excludes this entire overflow interval. This proves (1).

The boundary is sharp. At

    Pstar=L+Jbig=(3L-1)/2,

Pstar is the ternary word of N+1 ones. All N+2 positions of r double
with a carry, so the valuation is N+2 and the mask accepts, although
Pstar>=L. Pstar+1, whose lowest digit is two and whose other N digits
are one, also has valuation N+2. In particular, when N is even,
Pstar is odd and Pstar+1 is even: parity alone does not repair the
failure just beyond the sharp boundary.

The packing range used below is slightly stronger than (1):

    P0<3(L-1)/2=L+Jbig-1.                             (2)

At the excluded endpoint of this stated preliminary range, namely
P0=3(L-1)/2, the mask still rejects. Its first actual false acceptance
is one integer later, Pstar. These two endpoints are deliberately
distinguished.

## 2. A larger preliminary kernel lemma

Retain all ten equations and 43 primitive instructions of the
base-three kernel. Write their mathematical parameters as

    D0=3q^4, U=wD0, Y=sD0, E=UY, Q=UY^2, P=2Q+1,
    a=Y(U+1), A=a+3, D=A^2-1, M=6a+8, J=2r+1.

The letter P here denotes the first Pell parameter, distinct from P0.
The kernel implication and its positive even-r converse remain valid
under the following larger preliminary conditions:

    q>=3, r>=83, r<2D0, D0<r^2.                        (3)

In particular the scale is not assumed square. The new upper limit in
(3) is stronger than needed for the packing application, but makes the
endpoint counterexample below transparent.

Here is a check of every inherited step. Since D0>=243,

    U,Y>=D0,
    E>=D0^2>r+1,
    a>=D0(D0+1)>2r+1.                                 (4)

The triangular first norm still gives k=psi_P(t). Its congruence modulo
E implies t=r+1+vE with v>=0. The main norm gives c=psi_A(p), and
P>A together with c>Yk>k implies p>=t+1>=r+2>=85. Thus

    c>A^6>AD^2, c>Y(r+1)>J, 0<2p<=c.

These are precisely the independent hypotheses of the generic relaxed
auxiliary-rank and half-parameter results. They recover p=J, without
using parity or prime-power decoding. If v>=1, E>r and

    (2P-1)-4A=4Y(U(Y-1)-1)-11>0

give c/k<1/2, contradicting the positive interval. Hence t=r+1.
Neither argument requires r<D0.

Set xi=(U+1)^(2r)/U^r. The same Pell estimates give

    c/k>xi,
    c/k<xi*(1+3/a)^(2r).

The only bound affected by the larger range is

    6r/a<12/(D0+1)<=12/244<1/2.                        (5)

Consequently the elementary binomial estimate still yields

    c/k<xi*(1+12r/a),
    Y>=U^r, a>U^(r+1),
    0<c/k-xi<24r/(U+1).                               (6)

The elementary recurrence for chi_A(j)+(3-A)psi_A(j) gives 3^j modulo
M. The exponential equality therefore gives U=3^J modulo M. The
already proved bounds U<a<M and 3^J=3*9^r<U^(r+1)<a<M give U=3^J
as an integer equality. Since 3q^4 divides U, q is a power of three.

Now U>48r. The binomial expansion xi=F+T has 0<T<1/6 and
F=binom(2r,r) modulo U. Equations (6) and the positive interval
force Y=F, hence D0 divides the central binomial coefficient. This
proves the kernel implication under (3).

For the converse, suppose q is a power of three, r is even and satisfies
(3), and D0 divides binom(2r,r). Choose U=3^J and
Y=floor((U+1)^(2r)/U^r). The bound D0<r^2<U and the fact that D0,U
are powers of three make w=U/D0 a positive integer. The binomial
expansion makes s=Y/D0 a positive integer. All ratio estimates above
apply to the canonical choices c=psi_A(J), d=chi_A(J), k=psi_P(r+1).
They make eta=c-Yk and zeta=k-eta positive.

The unchanged formulas

    tau=(chi_P(r+1)-1)/2,
    h=(k-r-1)/E,
    gamma=(d-U-ac)/M

give positive integers by oddness of P, polynomial congruence, and
d-ac=3c-psi_A(J-1)>2c>U. Finally use m=2cJ,
f=chi_A(m), i=D*psi_A(m)/c^2, R=ic^2,
y_aux=psi_R(J), u=chi_R(J)/R, o=(u-c)/f, and j=(u-J)/c.
The divisibility, positivity, and two polynomial congruences are exactly
those in Section 7 of `EXPLORATION_BASE_THREE_PELL_KERNEL.md`.
They use J=1 modulo 4, which follows from even r, and do not use the
old upper bound r<D0. This constructs every positive witness under (3).

## 3. The enlarged input window closes before digit extraction

For the intended window, assume integers

    q>=3, q^3<=P0<3(q^4-1)/2,
    D0=3q^4, r=3P0+2.                                (7)

Before any power decoding, ordinary arithmetic gives the exact useful
bounds

    D0>=243,
    r>=3q^3+2>=83,
    r<(3D0-5)/2<3D0/2,
    D0<r^2.                                          (8)

The last follows from r>3q^3. Thus (3) holds. In this narrower window,
the initial ratio estimate even satisfies 6r/a<9/(D0+1)<1/2.
The kernel first proves q is a power of three and central-binomial
divisibility using only (8). Now (1)--(2) apply and prove P0<q^4
and every digit of P0 is native positive. The reasoning is therefore
not circular: P0<q^4 is obtained after the larger-range kernel proof.

Conversely, any even native positive word below q^4 automatically
satisfies the lower bound in (7), and satisfies its upper bound because
q^4<3(q^4-1)/2 for q>=3. The ordinary positive converse, or Section 2,
provides the full Pell tuple.

There is a complete positive counterfamily outside the sharp window.
For q=3^e with e>=1, let L=q^4, N=4e, and

    P0=(3L+1)/2=Pstar+1,
    D0=3L, r=(9L+7)/2.

Here P0 and r are even, every one of the N+1 digits of P0 is one
or two, and v_3(binom(2r,r))=N+2. Moreover r>=83,
r<2D0, and D0<r^2. Section 2 supplies every positive kernel
witness. Thus the five mask instructions and ten kernel equations
really do accept this overflowing P0 if its upper bound is omitted.
This counterfamily concerns that unbounded mask/kernel component,
not the bounded four-field relation below.

## 4. Four positive native fields with one shared slack

Take five positive input integers q,F0,F1,F2,F3. Introduce positive
auxiliaries H and alpha, and impose

    q=2H+1,
    R=F0+F3=F1+F2,
    R+alpha=q+H=3H+1.                                (9)

The value R is a computed register, not another supplied unknown.
Pack

    P0=F0+qF1+q^2F2+q^3F3.                           (10)

Positivity of H proves q>=3 and odd; no separate input guard is
needed. Positivity of alpha gives R<=3H. Positivity of the other
summand in each pair gives every Fi<=R-1<=3H-1<3H. Consequently

    P0>=1+q+q^2+q^3>q^3,
    P0<3H*(1+q+q^2+q^3)=3(q^4-1)/2.                 (11)

These are exactly the preliminary bounds (7). This shared bound
permits the important endpoint R=3H.

Apply the larger-window kernel. It first proves q=3^e with e>=1,
then (1) gives native positive digits in the whole word P0, of length
4e. We must still justify the four field boundaries. Its lowest q
chunk is at least H, the e-digit all-one repunit. If F0>=q, then
F0<3H<2q, and

    P0 mod q=F0-q<=3H-1-q=H-2<H,

a contradiction. Therefore F0<q, and F0 is exactly the first native
chunk. Removing that chunk leaves F1+qF2+q^2F3. The same argument
now proves F1<q, and then F2,F3<q. All four inputs therefore have
exactly e native digits. The divisions in this reasoning are proof
steps, not additional certificate computations.

The pair equality is also genuinely local. Write Fi=H+Ai, where
each Ai has Boolean ternary digits. Cancelling 2H from the two sides
of (9) gives A0+A3=A1+A2. Both sides have raw digits at most two,
so this is equivalent to a0+a3=a1+a2 at each position. Native raw
digits may exceed three before cancelling the common baseline; the
proof does not assume they were carry-free in that form.

In the converse direction, suppose q=3^e and the four input fields
are native words of length e, with equal pair sums R<=3H. Set
H=(q-1)/2 and alpha=3H+1-R>0. Equations (9) hold, and the packed
word is native. Since q is odd and the sum of the four fields is
2R, P0 is even. Its r is also even, so the positive kernel converse
supplies every remaining witness. This proves the exact bounded
relation on the five inputs, including its domains and parity.

The pair-sum bound does not follow for arbitrary native fields.
If a future compiler permits adding a common high zero Boolean column,
one column suffices to arrange it: replace q by 3q and every Fi by
Fi+q. The fields remain native and the pair sum becomes R+2q.
Since R<=2(q-1), while the new repunit is H+q,

    R+2q<=4q-2<3(H+q).

The added column preserves the local pair relation. This padding
observation is conditional on the eventual computation interface;
it is not an implemented raw-input or halting transformation.

## 5. Every counted operation

The following twelve instructions implement (9)--(10):

    twice_H=H+H, q_rhs=twice_H+1,
    R=F0+F3, R_alt=F1+F2,
    bound_rhs=q+H, bound=R+alpha,
    p0=q*F3, p1=F2+p0,
    p2=q*p1, p3=F1+p2,
    p4=q*p3, packed=F0+p4.

Compare q=q_rhs, R=R_alt, bound=bound_rhs. These cost three
multiplications and nine additions. Append the five native mask
instructions, using packed in place of the formerly supplied P0,
and the 43-operation base-three kernel. The complete count is

    12+5+43=60 operations,
    32 multiplications+28 additions/subtractions,
    14 free equality tests.

Besides the five positive input integers, there are 19 positive
auxiliaries: H,alpha and the 17 retained Pell witnesses. No packed
word bound, q guard, repunit, or parity test is left unpaid in this
60-operation relation. The lower-level 48-operation mask/kernel
remains conditional when used without these twelve instructions.

The checker verifies the complete schedule against fresh source
polynomials and the sole retained triangular residual correction.
It exhausts small complete mask ranges through both sharp endpoints,
checks preliminary bounds before power decoding, and enumerates
positive field pairs under the shared slack, including genuine
pre-decoding overflow examples. It also checks the explicit even
endpoint counterfamily's hypotheses without materializing its
enormous Pell witnesses. These finite tests support the proofs;
they do not establish a universal machine or a new universal bound.
