# A complete 63-operation bounded carry/borrow relation

The native ternary mask, a shared pair bound, and the carry/control equations
give a complete bounded increment relation in 63 operations. The corresponding
borrow relation has the same cost. Each has 32 multiplications and 31
additions/subtractions, three positive parameters, twenty-one positive
unknowns, and fifteen equations.

This is an exact one-step counter relation. It is not a complete machine
history, a raw-input converter, or a universal certificate. The counter's
bits are stored in ternary positions but interpreted with binary significance.
That distinction remains part of the stated interface.

## 1. Exact endpoint meaning

For 0<=n<2^m, let

    code_m(n)=sum_(j=0)^(m-1) bit_j(n)*3^j.

The parameters q,F_A,F_B may be arbitrary positive integers. The increment
system has positive witnesses if and only if, for some m>=1,

    q=3^m, J=(q-1)/2,
    F_A=J+code_m(n), F_B=J+code_m(n+1),
    0<=n<2^m-1.                                      (1)

The borrow system has the same description with n+1 replaced by n-1 and
1<=n<2^m. In particular, zero increment inputs are allowed, increment
overflow is excluded, and a borrow from zero is excluded. There is no
external Booleanity promise on F_A,F_B and no external assumption q>=3.

## 2. Source equations and complete arithmetic

Supply positive outer unknowns J,F_D,F_E,alpha, and the seventeen positive
Pell unknowns

    a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,gamma,y_aux.

The four finite source equations for increment are

    q=2J+1,
    F_E+J=2F_D+1,
    F_A+F_E=F_B+F_D=S,
    S+alpha=q+J.                                     (2)

Here S denotes the already computed left pair sum, not an additional
unknown. For borrow, replace the third equation by

    F_A+F_D=F_B+F_E=S.                               (3)

Keep the same packing in both modes:

    P0=F_A+qF_B+q^2F_D+q^3F_E,
    L=q^4, D0=3L, r=3P0+2.                          (4)

The last equality in (4) is the fifth source equation. The ten remaining
equations are the unchanged base-three Pell kernel. To state them explicitly,
use the mathematical abbreviations

    U=wD0, Y=sD0, E_pell=UY,
    A_pell=a+3, M=6a+8, D_pell=A_pell^2-1,
    u=2r+1+jc, K=D_pell*(f^2-1).

Then assert

    tau(tau+1)=(E_pell^2+U)(Yk)^2,
    c=Yk+eta, k=eta+zeta,
    k=r+1+hE_pell,
    a=Y(U+1),
    d=U+ac+gamma M,
    d^2=1+D_pell*c^2,
    (ic^2)^2=D_pell*(f^2-1),
    K*(u^2-y_aux^2)=1-y_aux^2,
    u=c+of.                                          (5)

The complete checker is
`../verification/explore_native_ternary_ripple.py`, with an adjacent JSON
receipt for both modes. It contains all primitives and fresh source
polynomials for (2)-(5). The count is

| Part | Operations |
|---|---:|
| q=J+J+1 | 2 |
| Native seed F_E+J=F_D+F_D+1 | 3 |
| Two pair sums | 2 |
| Shared bound S+alpha=q+J | 2 |
| Four-field Horner packing | 6 |
| Native mask and powers | 5 |
| Retained Pell kernel | 43 |
| Total | 63 |

The two doublings in this schedule use addition. All fixed numeral
multiplications elsewhere are counted. No division by two, exponentiation,
or digit extraction occurs as a primitive. As before, the penultimate
Pell residual has only the acyclic adjustment

    ((ic^2)^2-D_pell*(f^2-1))*(u^2-y_aux^2).

## 3. An overflow interval rejected by the native mask

Let L=3^N and J_L=(L-1)/2. For

    L<=P0<L+J_L,

the valuation of binom(2r,r), r=3P0+2, is at most N, so it cannot be
divisible by D0=3L=3^(N+1).

To prove this, write P0=L+t with 0<=t<J_L. The ternary digits of r
are the initial digit 2, the N digits of t, and an extra top digit 1.
Compare t with the N-digit repunit J_L. Its highest differing digit is
zero, and every higher digit is one. When r is doubled, that zero digit
produces no outgoing carry regardless of the incoming carry. The higher
one digits cannot restart a carry, nor can the extra top one. Thus at
least two of the N+2 possible carry positions fail. Kummer's theorem
gives the asserted valuation bound.

The strict upper endpoint matters. At P0=L+J_L every digit after the
initial 2 is one, so all N+2 positions carry and the divisibility test
accepts an overflow. The source bound below stays strictly away from
this endpoint.

## 4. Bounds derived solely from positive source equations

Because J is a positive integer and q=2J+1, q>=3 without an external
range assumption. The shared slack and pair equality give

    S<=q+J-1=3J,
    0<F_A,F_B,F_D,F_E<3J.                           (6)

Each field is strictly smaller than S because the other member of its
pair is positive. No field bound F_i<q has been assumed.

Every field is positive, so P0>=q^3. On the other hand, (6) yields

    P0 < 3J*(1+q+q^2+q^3)
       = 3(L-1)/2.                                  (7)

Consequently D0>=243 and

    r>=3q^3+2>=83,
    r<3D0/2,
    D0<r^2.                                         (8)

The inequality D0<r^2 follows already from r>3q^3. These are the only
enlarged range estimates needed before applying the Pell arguments.

For clarity, the 48-operation proof cannot be invoked with its old
P0<L hypothesis at this stage. Instead use the retained kernel with
the preliminary estimates (8), as follows. Arbitrary positive witnesses
have U,Y>=D0 and

    E_pell>=D0^2>r+1,
    a>=D0(D0+1)>2r+1,
    6r/a<9/(D0+1)<=9/244<1/2.                       (9)

The first norm and index congruence give a first Pell index at least
r+1. The main norm's base is smaller and c>Yk, so its index is at
least r+2>=85 and c>A_pell^6>A_pell*D_pell^2. These are the generic
relaxed-rank and half-parameter hypotheses. They recover the exact
main index 2r+1. The inequality E_pell>r and the unchanged positive
difference

    (2P_pell-1)-4A_pell=4Y(U(Y-1)-1)-11

recover the exact first index r+1. The ratio lower bound gives
Y>=U^r and a>U^(r+1); (9) gives the same upper error
0<c/k-xi<24r/(U+1), xi=(U+1)^(2r)/U^r.

The recurrence exponent argument now gives U=3^(2r+1), because both
it and the congruent power lie in (0,6a+8). The fractional binomial
tail is below 1/6, the ratio error is below 1/2, and the interval
forces exact rounding. Hence

    q is a power of three,
    D0 divides binom(2r,r).                         (10)

These steps are precisely the kernel proof of
`EXPLORATION_BASE_THREE_POSITIVE_KERNEL.md`, with every occurrence
of its old r<D0 preliminary estimate replaced by the explicitly sufficient
estimates (8)-(9). They use neither field decoding nor parity. The
separate `EXPLORATION_NATIVE_TERNARY_OVERFLOW.md` develops the same
enlarged kernel and shared-packing interface independently.

## 5. Recover bounded native fields without assuming away their carries

Now q=3^m, m>=1, and L=3^(4m). Equations (7) and (10), together with
Section 3, exclude P0>=L. For P0<L, the native mask theorem makes
every one of its 4m ternary digits 1 or 2.

Therefore each of its four base-q chunks lies between J=(q-1)/2 and
q-1. To recover the supplied fields, start with F_A. By (6), F_A<3J<2q.
If F_A>=q, its remainder modulo q is at most

    3J-1-q=J-2,

which is smaller than the first native chunk's minimum J. This is
impossible. Thus F_A<q and it creates no carry into the next chunk.
Repeat the identical argument for F_B, then F_D, then F_E. This proves

    J<=F_A,F_B,F_D,F_E<q,

and makes every field a native ternary word. This induction is essential:
before the mask, (6) permits some fields above q. The proof does not
silently treat a Horner sum of unbounded fields as concatenation.

Define the mathematical decoded Boolean words

    A=F_A-J, B=F_B-J, D=F_D-J, E=F_E-J.

These can be zero; none is a supplied positive witness. The source seed
becomes E=2D+1. The pair equality becomes A+E=B+D for increment or
A+D=B+E for borrow.

## 6. Exact ripple and all-positive necessity

The Boolean classification proved in
`EXPLORATION_TERNARY_COUNTER_CONTROL.md` gives

    D=(3^k-1)/2, E=3^k, 0<=k<m.                    (11)

It follows directly by propagating the carry in 2D+1: D has an initial
run of ones, the first zero produces E's unique one, and any later D one
would create a forbidden E digit two. Since E<q, that first zero occurs
within the width.

The pair equality has raw digits at most two on either side. Thus it is
digitwise exact in radix three. In increment mode, the first k bits of A
are one and become zero, its bit k is zero and becomes one, and higher
bits are unchanged. In borrow mode those first k bits are zero and become
one, and bit k is one and becomes zero. This proves the endpoint
description (1), including its nonoverflow and nonzero-borrow conditions.

Conversely take any endpoint pair in (1), or its stated borrow analogue.
Let k be the finite ripple's termination index and define D,E by (11).
Set F_D=J+D, F_E=J+E. These are positive native words even when D=0.
All local source equations hold. Define

    alpha=q+J-S.

In increment mode A and E are disjoint Boolean words: E occurs at the
first zero bit of A. Hence A+E<=J and S=2J+(A+E)<=3J. In borrow mode,
A and D are disjoint and the same argument gives S<=3J. Thus alpha>=1.

Keeping the extra unit in q+J=3J+1 is necessary to include every fixed-width
transition. For example, incrementing zero to one at width one has S=3J
and alpha=1. A stronger equation S+alpha=3J would incorrectly reject it.

All four fields are native and bounded, so P0<L and the native mask
gives the required central-binomial divisibility. In either mode the
pair equality makes F_A+F_B+F_D+F_E even. Since q is odd, P0 has this
same parity, hence r=3P0+2 is even. No parity equation is added.

Every hypothesis of the positive converse in the 48-operation note now
holds. Its explicit canonical construction supplies all seventeen
positive Pell witnesses. Together with positive J,F_D,F_E,alpha this
provides all twenty-one positive unknowns. No raw zero-valued counter
plane is used as a positive supplied unknown.

## 7. Independent finite boundaries and remaining machine interface

The checker verifies both complete 63-operation schedules against fifteen
fresh source polynomials. Its finite phase checks 5,168 positive outer
tuples at odd q from 3 through 31 before assuming prime powers. It then
enumerates 31,460 complete parameter/helper candidate pairs at widths
one through four; the 52 accepted candidates are exactly all valid bounded
increment/borrow transitions at those widths. It also constructs 1,004
canonical ripples through width eight, including 72 cases with alpha=1.
The check evaluates the full mask valuation, not just separate local fields.

No enormous Pell tuple is numerically instantiated. Its existence is proved
by the general positive converse, while the finite tests verify the exact
inputs to that theorem. These evidence boundaries are distinct.

A complete machine would still need multiple instructions, their control
flow and repeated histories, register selection, a faithful raw-number
input interface, and an accepting event. In particular code_m(n) uses
ternary positions to store binary bits; its numerical value is generally
not n. The proved 63-operation relation is a bounded one-step arithmetic
component, not a new universal certificate.
