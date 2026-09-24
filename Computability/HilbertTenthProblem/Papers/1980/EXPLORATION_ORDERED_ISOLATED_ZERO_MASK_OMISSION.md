# Ordered ROM states and isolated zero requests still do not remove the Z mask

The counterexample in `EXPLORATION_ROM_ZERO_MASK_OMISSION.md` used a
positive coordinate difference within one ROM row and two consecutive
zero-request rows. This note removes both conveniences. All zero-request
states are placed below all nozero states, the complementary-zero port
is above every other port plus the state-coordinate span, and every
zero request has nozero neighbours in serial time. Every off-grid column
below the fixed ROM-product bound is forbidden as well. A malformed Boolean
`D` still absorbs a legitimate ROM cross term and permits a false zero
test when the `Z` mask is omitted.

The construction retains both Boolean track fields, both Boolean counter
guards, both sign masks, all four program masks, the positive pair
`Z+D=H`, the input bound, and the full cyclic route and counter time
equations. It works with the `D` mask retained, hence also when both
zero masks are omitted. It does not address deleting only the `D` mask
while keeping `Z` Boolean. No unchanged complete certificate is altered.

`../verification/explore_ordered_isolated_zero_mask_omission.py/.json`
checks the fixed ROM, exact local large-integer identities, all macro
endpoints and the symbolic whole-history induction. Unlike the previous
example, the resulting input and number of iterations are too large to
materialize the entire history. That evidence boundary is explicit; the
unbounded counterexample below is constructive.

## 1. The apparent interval argument has an unpaid premise

If `D` is Boolean and `gD` is Boolean, where
`g=(3^m-3)/6` is an interval of `m-1` one digits, then those intervals
must be disjoint. Indeed the first overlap of two intervals has raw
coefficient two, with no incoming carry. It cannot be a Boolean digit.
This conditional observation is correct.

The current source does not mask `T=J-gD` itself. It masks `A0`, `A1`,
`A0+T`, and `A1+T`. These conditions do not imply that `T` is Boolean:
already `T=2`, `A0=A1=1` give Boolean guards equal to three. The
counterexample uses this precise freedom on the nozero row following
the false zero request. It does not dispute the conditional interval
lemma.

## 2. A fixed graph with isolated requests and an empty predicate

There are thirty states, of phase `i mod 3`. Use the linear edges
`i -> i+1` for `0<=i<29` and the four extra edges

    11 -> 6, 23 -> 18, 29 -> 24, 29 -> 0.

State zero is the cyclic entry and terminal state. The five six-state
macros are:

| States | Signs | Effect on a bank `(n0,n1,0)` |
|---|---|---|
| 0–5 | `+++---` | preserving prefix |
| 6–11 | `+++-+-` | `(n0,n1+2,0)` |
| 12–17 | `+++---` | `(n0,n1,0)` |
| 18–23 | `−++---` | `(n0−2,n1,0)` |
| 24–29 | `+−+---` | `(n0,n1−2,0)` |

The zero-request states are exactly `{1,8,12,20,26}`. No directed edge
has zero requests at both ends, including the cyclic edge. State 1
is the usual valid prefix mark on the initially zero second register.
States 8, 20, and 26 test the third register before its temporary plus
step; it is zero at each such source. State 12 tests the first register.

Every accepting first return must pass state 12. The prefix and any
number of preparation loops leave its source first register equal to
`2x`. Thus for positive `x` this fixed labelled graph has no honest
accepting history, irrespective of its nondeterministic loop choices.

## 3. Ordered coordinates and a high zero port

Choose Sidon state coordinates on the spacing-four grid, with
`3^4>30`, and assign their five smallest values to the five zero
states. Give state 13 a coordinate below the nozero state 0. Write

    d0=a_0-a_13>0.

The maintained construction has `d0>=4`. Give the sign port coordinate
`bs>2 max(a_i)` and the zero port coordinate `bz>2bs`, avoiding the
finitely many sum collisions. The checker constructs and verifies an
explicit set of this form, including one-versus-two separation.
With the usual common shift `d=bz`, put `hz=3^(d+bz)`.

These choices ensure that every nonzero-label channel, including its
full state-coordinate span, lies below `hz`. On any active zero state,
all the complementary-zero cross terms are strictly below `hz` as
well, since their lookup states have larger coordinates. Thus the
proposed ordering and high-port property hold exactly.

However, at the following nozero state 13, the lookup term supplied by
nozero state 0 gives the ordinary junk bit

    3^(d+bz-d0) = hz/3^d0.

It is below the zero port but above all the other channels, and differs
from every forbidden position. For the chosen successor `13 -> 14`,
it is not removed by the genuine state, sign or zero outputs. The
checker verifies its coefficient is one.

The forbidden constant includes every off-grid position below a fixed
power of three exceeding all ROM products, as well as the ordinary
marker/port exclusions and a fresh high intrinsic-width bit. Every
correct single-state junk row lies on the spacing-four grid and avoids
that stronger constant. The bit `hz/3^d0` is on the grid. Thus the
construction also meets dense off-grid padding. More generally, adding
any fixed forbidden positions that all correct edge rows avoid cannot
prevent the subtraction below: its victim is itself a valid junk bit
on the correct edge `13 -> 14`, and removing a bit never adds forbidden
support. One simply chooses the frame large enough for the enlarged
fixed constant and defines `h` from that width.

Choose a sufficiently large frame `R=3^m` with all fixed products and
the fresh forbidden mask inside it, and set `h=m-d0>=3`. Then

    hz*3^h = R*3^(d+bz-d0).                       (1)

A malformed flag near the end of one row therefore becomes precisely
this legitimate low cross term in the next row. Raising the zero port
does not remove this identity; it changes the permitted width and
input together.

## 4. The numerical history and the single false request

Take the positive raw input and preparation count

    x=3^h, k=(3^(h-1)-1)/2.

Run the prefix once, preparation macro `k` times, states 12–17 once,
first-counter cleanup `x` times, and second-counter cleanup `k` times,
then return to state zero. Its duration and the first block of the
false-zero macro are

    u=12+6x+12k, b=6+6k.

All numerical counters remain nonnegative. At the false zero request
in row `b`, the first register is `2*3^h`. At the following nozero row
`b+1`, the second register is `2k=3^(h-1)-1`. Both are less than
`R/3`, as are every intermediate source value, since `d0>=4`. The
stronger paid margin `4x<R` also holds. The final bank is zero.

The only false request is state 12. Every other declared zero request
is on the explicitly zero third register, or the initial second
register in the prefix. This proves the assertions for the entire
finite history, not a bounded prefix of an otherwise unclassified run.

## 5. A backward cross-row flag changes two masks

Let the honest label words of this numerical path be `Dold` and
`Zold=H-Dold`, and let `Vold` be its correct ROM junk. The word
`Told=J-gDold`, with `g=(R-3)/6`, is the mask dictated by those
labels; its old guard at the false request need not be valid.
Put

    Delta=3^h R^b,
    Dnew=Dold+Delta, Znew=Zold-Delta,
    Vnew=Vold-hz*Delta, Tnew=Told-g*Delta.

The new bit is at offset `h` of a zero row, whose original D head
was zero. Thus `Dnew` remains Boolean and has an off-head bit.
Equation (1) shows that the junk subtraction removes exactly the
coefficient-one cross term in row `b+1`. Hence `Vnew` is Boolean and
retains every forbidden-column condition. The exact whole-word route
is preserved by

    Vnew+hz*Dnew=Vold+hz*Dold.

The positive pair and top source are preserved identically. `Znew`
is positive: a genuine later zero request occurs at row `b+8`, so
its head exceeds `Delta<R^(b+1)`. It is non-Boolean because borrowing
through row `b` creates a digit two at offset `h` there.

The key interval identity, now across a zero and a nozero row, is

    g*3^h = (Jrow-J_h)+R*J_(h-1),
    Jrow=(R-1)/2, J_j=(3^j-1)/2.                 (2)

Consequently the modified masks in those two rows are

    T_b=J_h, T_(b+1)=R/3-J_(h-1).                (3)

At row `b`, both source tracks equal `3^h`, and their guards are

    3^h+J_h=J_(h+1),                            (4)

which are Boolean. At row `b+1`, both source tracks equal `J_(h-1)`,
and both guards are exactly `R/3`, again Boolean. The second mask
in (3) has unit ternary digit two, so `Tnew` itself is not Boolean.
That is permitted by every retained source and mask.

Every other row retains its usual correct guard. Ordinary source
values are below `R/3`, and genuine zero requests have zero tracks.
All supplied raw fields remain strictly positive. The tracks already
contain a bit from the initial `2*3^h`, both signs occur, both zero
words are positive, and the ROM words retain their marker and support
bits. The counter time equation is unchanged because its entire
numerical walk and signs are unchanged.

## 6. Complete mask and positive-kernel interface

Use the eleven fields

    Kp,A0+Tnew,A0,A1+Tnew,A1,Km,Dnew,C,Vnew,TC,TV,

or omit D as well and use ten. Every listed field is a positive
Boolean word below `q=R^u`. The support fields remain
`TC=C+J-SH` and `TV=Vnew+Zstar H`; deleting a junk bit preserves
their Booleanity and positivity.

For either field count `f`, form `P` by base-q concatenation and put
`L=q^f`, `r=P+(L-1)/2`, `beta=L-r`. Exactly as in the preceding
full-ROM counterexample, every ternary digit of `r` is 1 or 2, its
unit is 2, `beta>0`, and `L` divides the central binomial coefficient.
The growth bounds are `q^(f-1)<r<L<r^2`.

There are `2+2k+x` declared zero labels in the described path, an odd
number because `x` is odd. Since `u` is even, both `Znew` and
`Dnew` are even after the added/subtracted odd pulse. The first six
fields have even total parity, and the four program fields sum to
`2(C+Vnew)+J+(Zstar-S)H`, also even. Thus both altered indices are
even. The fixed-sign 43-operation positive converse applies with
the actual power-of-three scale `D0=L`; it supplies every positive
Pell auxiliary. No square-scale or unproved parity hypothesis is used.

Doubling every raw coordinate preserves the same obstruction and
the exact routing/top identities; its stronger input bound was
already checked. In particular evenness of the emitted complement
does not eliminate this example.

The complete histories and values `q` are enormous but explicitly
finite. The numerical regression deliberately checks the fixed table,
all possible traversed edge rows, the two altered large-integer guard
rows, and the affine macro induction. It does not claim to instantiate
`q`, the entire packed history, the central binomial integer, or the
Pell auxiliaries. Those are established by the general construction.

This rules out the stated repairs consisting solely of ordered state
coordinates, a high zero port, isolated requests and globally safe
fixed forbidden-column padding. Stronger
restrictions on the numerical value of the next register, a separately
typed T word, or different output machinery would be additional
conditions and are not refuted here.
