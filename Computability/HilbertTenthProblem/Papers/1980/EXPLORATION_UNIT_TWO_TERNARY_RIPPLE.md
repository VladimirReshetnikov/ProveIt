# A complete 62-operation bounded ripple using a unit-two field

This construction saves one operation from the complete63-operation
native ripple. It keeps the native fields FA,FB,FC,FE, replacing FD
by the union C of the carry and control bits. This choice is different
from the refuted variant in `EXPLORATION_NATIVE_RIPPLE_UNMASKED_CARRY.md`,
which retained FD and omitted the necessary FE mask.

Both increment and borrow have62 operations,31 multiplications and31
additions/subtractions,15 equations,3 positive parameters and21 positive
unknowns. This is a complete bounded one-step relation, not a universal
machine, a raw numerical loader, or a complete computation history.

## 1. Exact endpoint relation and equations

Let code_m(n)=sum_j bit_j(n)*3^j for0<=n<2^m. The parameters q,FA,FB
are arbitrary positive integers. The increment system has positive
witnesses exactly when, for some m>=1,

    q=3^m, H=(q-1)/2,
    FA=H+code_m(n), FB=H+code_m(n+1),
    0<=n<2^m-1.                                      (1)

For borrow, replace n+1 by n-1 and use1<=n<2^m. Zero increment
inputs are included; overflow and borrowing from zero are excluded.

Supply positive H,FC,FE,alpha and the17 retained positive Pell
witnesses, including r. The finite increment equations are

    q=2H+1,
    3FE=2FC+(H+1),
    FA+2FE=FB+FC+H,
    FA+FE+alpha=q+H.                                 (2)

For borrow, interchange FA and FB in the last two equations, giving
FA+FC+H=FB+2FE and FB+FE+alpha=q+H.
In both modes construct

    P0=FC+qFA+q^2FB+q^3FE,
    D0=q^4, r=P0.                                    (3)

Use the minus-sign43-operation kernel from
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`. In its notation the last
two auxiliary comparisons use

    u=jc-(2r+1)=of-c,
    (ic^2)^2*(u^2-y_aux^2)=1-y_aux^2.                 (4)

All other kernel equations are the general-scale base-three equations
in that note. The scale D0 is computed, not supplied as an extra
unknown. The equality r=P0 costs no arithmetic.

## 2. Exact operation accounting

Compute Hplus1=H+1 and q_rhs=Hplus1+H, two additions. The local
equation uses four additions: for increment set S=FA+FE,
local_lhs=S+FE, local_pair=FB+FC, local_rhs=local_pair+H.
For borrow interchange FA and FB in these instructions.

The seed requires three operations:

    three_E=3*FE, twice_C=FC+FC, seed_rhs=twice_C+Hplus1.

It reuses Hplus1 from the geometry; multiplication by three is counted.
The shared bound requires bound=S+alpha and bound_rhs=q+H, two
additions. Horner packing needs three multiplications and three additions.
The powers q2=q*q,D0=q2*q2 need two multiplications.

Thus the complete count is

    2 geometry+4 local+3 seed+2 bound+6 packing+2 powers+43 Pell
      =62=31 multiplications+31 additions/subtractions. (5)

There are four finite comparisons, r=P0, and ten kernel comparisons.
No field guard, repunit, parity equation, or zero adapter is omitted.
The checker is `../verification/explore_unit_two_ternary_ripple.py`.

## 3. Bounds and parity from positive source equations

For a unified calculation write X=FA,Y=FB in increment mode and
X=FB,Y=FA in borrow mode. Let S=X+FE. Positivity gives

    q=2H+1>=3, S<=3H,
    0<X,FE<3H.

The seed and local equations give the exact rational identities

    FC=(3FE-H-1)/2,
    Y=X+(FE-H+1)/2.                                  (6)

These are proof identities, not division instructions. They imply

    FC<=4H-2<4H,
    Y<= (5H-FE+1)/2 <=5H/2<3H.

Consequently both FA,FB and FE are positive and smaller than3H,
while FC can initially be as large as4H-2. Since these quantities
are integers, packing gives

    P0>=1+q+q^2+q^3>q^3,
    P0 <= (4H-2)+(3H-1)(q+q^2+q^3)
        = 3H(1+q+q^2+q^3)+H-2-(q+q^2+q^3)
        < 3(q^4-1)/2.                                (7)

Thus D0>=81,r>=27,r<3D0/2<2D0 and D0<r^2. The latter follows
from r>q^3. These are precisely the general-scale kernel bounds,
including q=3. The old thresholds D0>=243,r>=83 are not imposed.

The source also forces r to be odd. Modulo2 the seed gives
FE=H+1, and the local equality gives FA+FB+FC=H. Their sum is
one modulo2. Since q is odd, the Horner packing has the same
parity as the field sum. Therefore P0=r is odd, before any digit
decoding. This is why the fixed minus-sign kernel is used.

## 4. Decode the whole word before its fields

The general-scale kernel first proves q is a power of three and
D0 divides binom(2r,r), using (7) and positivity only. The direct
unit-two mask and its overflow theorem then give

    P0<q^4,
    every ternary digit of P0 is1 or2,
    its unit digit is2.                              (8)

No native field or no-carry assumption was used to reach (8).

Because FE is the highest field and all other terms in the packing
are positive, P0<q^4 immediately gives FE<q. The seed now sharpens
the problematic first-field bound:

    FC=(3FE-H-1)/2 <=(5H-1)/2<3H.

All four supplied fields are therefore smaller than3H. The standard
lowest-chunk induction now applies. Each native base-q chunk is at
least H. If its supplied field Fi were at least q, then Fi<3H<2q
would give a remainder at most3H-1-q=H-2, which is impossible.
First this proves FC<q and identifies the lowest chunk, then FA,
then FB; FE is the remaining top chunk. Hence all four fields are
native words of the same width. This is a proof step and involves
no uncounted division in the arithmetic schedule.

Write FC=H+C,FE=H+E,FA=H+A,FB=H+B with Boolean ternary words.
The seed becomes

    3E=2C+1.                                         (9)

The local equality becomes A+2E=B+C for increment, and A+C=B+2E
for borrow. Its raw sides are not assumed carry-free at this point.

## 5. Recover the omitted carry word and the exact ripple

Equation (9) with Boolean C,E has exactly the forms

    C=(3^(k+1)-1)/2, E=3^k, 0<=k<m.                 (10)

Indeed its right side is divisible by three, so the unit digit of C
must be one. In2C+1, the initial run of one digits propagates the
initial carry, until the first zero creates a single one and stops
it. Any later one digit of C would create a forbidden digit two in
3E. The run can fill the whole width, terminating immediately above
it. Thus2C+1=3^(k+1) and (10) follows, including k=m-1.

The omitted word is now recovered in the proof as

    D=C-E=(3^k-1)/2,

a Boolean word. Subtract E from each local side. Increment gives
A+E=B+D and borrow gives A+D=B+E. These sides have raw digits at
most two, so they are now carry-free. The first k bits flip through
the ripple; bit k terminates it; higher bits are unchanged. This
proves exactly (1) and its borrow analogue. In particular the
unmasked carry word is recovered here, unlike in the refuted62 variant.

## 6. Every positive witness in the converse

Start with any bounded endpoint pair in (1) or its borrow analogue.
Let k be its termination index and choose C,E by (10). Set
FC=H+C,FE=H+E. These are positive native fields even when the
ordinary carry D is zero, and the seed and local equations hold.

For increment A and E are disjoint Boolean words, because E marks
the first zero of A. Thus S=FA+FE=2H+A+E<=3H. For borrow the
new counter B has zero at the termination bit, so B and E are
disjoint and S=FB+FE<=3H. Set alpha=q+H-S>=1.

The packing is native and its unit is two because C has unit one.
Its parity is odd by the source equations. Hence r=P0 is odd and
D0=q^4 divides binom(2r,r). The bounds (7) apply. The full
minus-sign positive converse of the unit-two kernel supplies all17
positive Pell witnesses, with

    o=(u+c)/f, j=(u+(2r+1))/c.

This proves necessity at every width, without a parity promise on the
endpoint parameters or a nonnegative supplied variable. At width one,
q=3,H=1: increment0 to1 has FA=1,FB=2,FC=FE=2,alpha=1 and P0=77;
borrow1 to0 has FA=2,FB=1,FC=FE=2,alpha=1 and P0=71.

## 7. Verification scope

The checker verifies both62-operation schedules against all15 fresh
source polynomials, including the signed auxiliary correction. Its
finite phase enumerates complete positive outer candidates at small
widths, directly evaluates the whole packed mask, and compares the
accepted endpoints to the bounded binary increment/borrow relation.
It also constructs canonical ripples through eight bits, including
both smallest q=3 examples and cases with alpha=1.

The separate unit-two checker verifies both signed43 cores and small
exact auxiliary constructions. No enormous full Pell tuple is
materialized for the counter cases; its existence follows from the
general theorem and the checked hypotheses. Raw numerical input is
still not code_m(n) without a separately proved conversion. Neither
an arbitrary machine history nor a universal operation bound is claimed.
