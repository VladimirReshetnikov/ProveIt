# Dedicated zero-valued branching does not close the D-only hole

Restricting every multi-successor state to a true-zero request on a dedicated
fourth counter does not by itself make the `D` mask redundant. A destination
column needed as junk by such a branch can be used as a hole in a different,
deterministic nozero row. The interval carry compensation then occurs at
that deterministic row's positive counter, rather than at the zero-valued
dispatch counter.

This note gives a fixed forty-state, four-counter example. It retains
ordered zero coordinates, marker capacity `3^4=81>40`, and a fixed forbidden
word containing every off-grid position in the complete fixed product span.
The companion is `../verification/explore_zero_dispatch_d_mask_omission.py`
and its JSON receipt. Its claim is confined to the stated convolution
controller and D-only omission; it does not rule out a new edge-based
controller or establish any smaller operation count.

## 1. A graph whose only branches test the fourth counter at zero

State `i` acts on counter `i mod 4`. The signs are:

| States | Signs | Effect |
|---|---|---|
| 0--3 | `++++` | initial prefix |
| 4--11 | `-+--++++` | add two to counter one |
| 12--19 | `----++++` | identity |
| 20--27 | `-----+++` | subtract two from counter zero |
| 28--35 | `----+-++` | subtract two from counter one |
| 36--39 | `----` | final suffix |

All successive edges `i -> i+1` are present, together with

\[
 11\to4,\quad27\to20,\quad27\to36,
 \quad35\to28,\quad39\to0.
\]

The zero-request states are

\[
 \{1,2,3,11,16,18,19,27,35\}.
\]

Only states `11,27,35` have multiple successors. All three have phase
three, so they operate on the fourth counter. After the prefix, that counter
is one at the start of every eight-state block. The first-half decrement
changes it to zero; the second-half increment occurs at its zero-valued
last state. Thus every branch in every concatenation of these blocks acts
on the fourth counter at zero. The final suffix decrements its value one
to zero. All states with nonzero source values are deterministic.

Every positive return to state zero must pass state sixteen. From the raw
initial state `(2x,0,0,0)`, the prefix makes counter zero `2x+1`; pump
cycles preserve it, and the first half of the bad block makes it `2x`.
State sixteen requests zero there. This is false for every positive input.
Therefore the program is honestly empty despite the dedicated-zero branch
restriction.

## 2. An explicit false path and its local guard repair

Choose a sufficiently large `R=3^m` and an exponent `2 <= h <= m-2`, to
be specified by the fixed ROM below. Put

\[
 x=3^h,\qquad j=(3^{h-1}-1)/2.
\]

Use the prefix once, `j` pump blocks, the bad block once, `x` counter-zero
cleanup blocks, `j` counter-one cleanup blocks, and the suffix once. Apart
from the request at state sixteen, this is an ordinary nonnegative path
from `(2x,0,0,0)` to `(0,0,0,0)`.

The source vectors at the successive block boundaries are

\[
\begin{split}
 (2x+1,1,1,1)&\longrightarrow(2x+1,2j+1,1,1),\\
 (2x+1,2j+1,1,1)&\longrightarrow(1,2j+1,1,1),\\
 (1,2j+1,1,1)&\longrightarrow(1,1,1,1)
 \longrightarrow(0,0,0,0).
\end{split}
\]

At the false zero row, state sixteen, the source vector is
`(2x,2j,0,0)`. The following row, state seventeen, is deterministic and
nozero-labelled; its active source counter has value `2j=3^{h-1}-1`.
The two ordinary Boolean numerical tracks therefore have values `3^h`
at the false row and `(3^{h-1}-1)/2` at the following row.

The false row number and duration are

\[
 b=8+8j=4\cdot3^{h-1}+4,
 \qquad u=16+8x+16j=32\cdot3^{h-1}+8.
\]

The duration is a multiple of eight. The largest source value is at most
`2x+1<R/3`, and both `2x<R` and `4x<R` hold.

Use the same perturbation as in
`EXPLORATION_ROM_D_MASK_GRID_HOLE.md`:

\[
\begin{array}{ll}
 \Delta=3^hR^b,&Z=Z_{\rm old}+\Delta,\\
 D=D_{\rm old}-\Delta,&T=T_{\rm old}+(R-3)\Delta/6,\\
 V=V_{\rm old}+h_z\Delta.
\end{array}
\]

Here `Z_old` contains the program's declared zero heads, and
`T_old=J-(R-3)D_old/6`. The single false interval is repaired exactly by
the two identities

\[
\begin{split}
 (R-1)/2+(R-3^h)/2+3^h&=R+(3^h-1)/2,\\
 R/3+2(3^{h-1}-1)/2+1&=R/3+3^{h-1}<R.
\end{split}
\]

Thus both whole guards `A_i+T` are Boolean. The new `Z` is Boolean; the
positive `D` borrows from the following nozero head and has digit two.
Every other declared zero is true, so all untouched intervals are correct.
The pair, top interval, and routing expressions remain exactly invariant.
No Booleanity of the unmasked `T` is presumed.

The numerical time equation is now

\[
 R^4(A_0+A_1+K_+-K_-)=A_0+A_1-2x.
\]

It holds by the ordinary four-counter telescoping recurrence; the
perturbation changes none of its coordinates.

## 3. The hole comes from a different true-zero branch

Construct the same Sidon convolution ROM as in the preceding grid-hole
note, now with forty state coordinates and two output coordinates. Assign
all zero-request coordinates below all other state coordinates. Use grid
spacing four, forbid every non-grid position through the full product
span, and add both output ports and a sufficiently high fixed forbidden
bit. All forty-four correct edge rows have positive Boolean junk disjoint
from this forbidden word.

Let

\[
 c=d+a_{12},\qquad h_z=3^{d+b_z},
 \qquad h=m-(b_z-a_{12}).
\]

The column `c` is required as ordinary unchosen junk by the genuine
zero-branch edge `11 -> 4`, because the alternative `11 -> 12` exists.
Consequently a globally safe fixed forbidden mask cannot include `c`.

The deterministic edge `17 -> 18` has no output at `c`: there is no
edge `17 -> 12`, and Sidon isolation excludes an accidental contribution
from another table term. The checker verifies this directly. Hence the
perturbation adds a previously absent, globally allowed junk bit in that
different row:

\[
 h_z\Delta=3^cR^{b+1}.
\]

Both `V` and `V+Z_*H` remain Boolean. The fact that the branch providing
the permission for `c` is true-zero does not affect the positive source
counter used by the interval repair in row seventeen.

For the exact fixed constants in the receipt,

\[
\begin{array}{rl}
\text{product span}&=61268,\\
|\operatorname{supp}(Z_*)|&=45954,\\
m&=61278,\\
d+b_z&=50472,\\
c&=39296,\\
h&=50102.
\end{array}
\]

The missing table exponent `c-a_17` is not an existing coefficient. Adding
it is not merely padding an already permitted ordinary transition: it
would create a selectable destination output `17 -> 12` in the unchanged
route relation. Such a table modification changes the controller and
requires a new soundness argument. This note only needs the directly
checked fact that the present dense-forbidden controller has the hole.

## 4. All positive outer and kernel witnesses

The sign words, tracks, guards, zero word, and four program words are the
same eleven retained fields as in the preceding D-only examples. All are
strictly positive Boolean words below `q=R^u`. Positivity follows from the
initial value `2x`, both signs, the explicit true-zero prefix, untouched
heads, and the ordinary positive ROM junk. The input slack is positive,
and `q=R^4v` has a positive quotient because `4` divides `u`.

Pack the eleven fields into `P`, set `L=q^11`, and put
`r=P+(L-1)/2`. The unit digit of `r` is two because the prefix begins
with a plus step. All other digits below `L` are one or two. Since the
state word is sparse, the packed slack `L-r` is positive. The exact
valuation is `v_3 binom(2r,r)=11mu`.

The even-parity condition is explicit. The number of declared zero rows
before the perturbation is

\[
 6+2j+x.
\]

Here the six fixed requests comprise the three true prefix requests and
the three bad-block requests at `16,18,19`; only request sixteen is false.
Adding the extra off-head zero bit gives `7+2j+x`, which is even because
`x` is odd. Thus the value of the new `Z` is even. The first six packed
fields have sum `H+2(A_0+A_1+T)`, and the four program fields have sum
`2(C+V)+J+(Z_*-S)H`; both sums are even since `u` is even. The wide
repunit is even as well. It follows that `r` is even.

At scale `L`, all hypotheses of the positive fixed-sign forty-three-
operation converse in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md` hold:
`L>=81`, `r>=27`, `r<L<r^2`, even parity, and the exact central
divisibility. This gives all remaining strictly positive kernel witnesses.
Doubling the raw coordinates gives the corresponding zero-or-two version.

The result is a complete false-witness family for D-only omission, even
under the dedicated-zero branching restriction. It remains a statement
about the specific vertex/convolution controller. No assertion is made
about a representation that supplies selected edges directly, tests
different ports, or changes the global history relation.

## 5. Reproduction and limits of finite evidence

The author regression returns `PASS_ZERO_DISPATCH_D_ONLY_COUNTERFAMILY`.
It checks all forty-four fixed ROM edge rows, 436 local interval cases,
128 complete finite controls, 2,240 true-zero branch visits, and four
symbolic perturbation identities. The marker-capacity inequality is
explicitly asserted.

The actual input is `3^50102`, its false row is `4*3^50101+4`, and the
duration is `32*3^50101+8`. These enormous complete words and their Pell
witnesses are not materialized. Their general properties follow from the
cycle invariants, the exact two-row calculation, the fixed-row support
checks, and the general kernel converse. Finite regression counts do not
stand for exhaustive searches over alternative encodings.
