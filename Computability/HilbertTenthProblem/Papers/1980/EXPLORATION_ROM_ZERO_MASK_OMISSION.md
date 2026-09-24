# The complete ROM does not replace the zero-event masks

This note gives a full positive outer counterexample to deleting the
mask on `Z`, even if the complementary word `D` remains Boolean. It also
works when both zero-event masks are omitted. The cyclic controller,
its two support tests, all counter guards, the input and time equations,
the positive pair `Z+D=H`, and the top-mask equation remain in force.
The malformed computation takes a zero branch on a strictly positive
counter. Thus this is stronger than the standalone convolution
counterexamples in `EXPLORATION_ZERO_MASK_TYPING.md`.

The counterexample changes which fields are packed. It makes no claim
about the unchanged 105, 104, or doubled-coordinate certificates, which
retain the relevant masks. Nor does it assert an optimized operation
count for the incorrect variants. Its exact source-interface regression
is `../verification/explore_rom_zero_mask_omission.py/.json`.
The opposite single deletion, retaining the `Z` mask while omitting only
the `D` mask, is not settled here: this witness deliberately has a
non-Boolean `Z` and would fail that retained mask.

## 1. A specific fixed graph recognizing no positive input

Use eighteen states, numbered 0 through 17, of phases `i mod 3`.
There are the edges `i -> i+1` for `0<=i<17`, and the two edges
`17 -> 12`, `17 -> 0`. The initial and cyclic terminal state is 0.
The signs are

    + + + - - -   + + + - - -   - + + - - -.

The zero-request states are exactly 1, 2, 6, 7, and 8. All other
states have complementary label `D=1`. The first six states are the
usual global plus/minus prefix. Its requested zero tests on registers
1 and 2 are true. In particular it includes the mandatory marked
initial zero test used to ensure the positive word `Z`.

Every positive first return must traverse state 6. On entering that
state the prefix has restored the input vector `[2x,0,0]`. State 6
requests that register 0 be zero. Consequently there is no honest
accepting path for any positive `x`. This is an empty-predicate fixed
controller, not a controller whose successful computation merely has
an alternative honest zero labelling.

Ignore that one zero request temporarily. For any positive `x` there
is a nonnegative numerical walk

    0,1,...,11, (12,13,14,15,16,17)^x, 0.

After states 6 through 11 the vector is again `[2x,0,0]`. Each final
six-state cycle subtracts two from register 0, while the other two
registers make a plus/minus excursion and return to zero. The only
false zero request is state 6, with source value `2x`. All signs,
phases, initial and final vectors, and every other zero request are
already correct.

## 2. Fixed Sidon constants with a useful cross term

The checker constructs twenty Sidon coordinates on the spacing-three
grid, with `3^3>18`, and with every coordinate between `a_min` and
`2*a_min`. Eighteen are state coordinates; the other two are the sign
and complementary-zero targets. Its coordinates are

    1425,1515,1434,1446,1461,1485,1428,1557,1620,1665,
    1713,1791,1866,1968,2034,2178,2292,2505,2625,2847.

In particular `a_6-a_0=3`. The checker verifies the complete Sidon
condition, the one-versus-two separation, nonnegative distinct ROM
exponents, and the spacing condition. It then constructs the usual
edge, count-marker, sign, and complementary-zero terms. The forbidden
word `Zstar` contains both label targets, the two high marker digits,
and a fresh high digit above the existing fixed size thresholds.
Choose a sufficiently large power `R=3^m` so that all row products
and support masks fit. The width is free to increase; no small-width
escape is being used.

Let `hz=3^(d+bz)`. Because state 0 emits complementary-zero label 1,
`K` contains `3^(d+bz-a_0)`. Multiplying by the active singleton
`3^a_6` produces

    hz*3^3.

This is an ordinary cross term in row 6's junk word. It is neither
the actual complementary-zero target nor any forbidden position.
The exact table checks verify that its coefficient is one. This is
the piece of ROM output that will absorb a malformed flag.

## 3. The flag and junk modification

Take `h=3`, `x=3^h=27`, and the numerical path above. Its duration is
`u=12+6x=174`. Put

    q=R^u, W=R^3, J=(q-1)/2, H=(q-1)/(R-1),
    g0=(R-3)/6, delta=3^h R^6.

Let `Dold` be the honest complementary label word of this path,
and `Zold=H-Dold`. Let `Vold` be the ordinary ROM junk. Define

    Dnew=Dold+delta, Znew=Zold-delta,
    Vnew=Vold-hz*delta,
    Tnew=J-g0*Dnew=Told-g0*delta.

`Dnew` is Boolean: row 6's old head digit was zero, and its new bit
is at offset `h`, not at a head. `Vnew` is Boolean because precisely
the cross term from Section 2 is removed. Its forbidden positions
remain zero. The identity

    Vnew+hz*Dnew=Vold+hz*Dold

preserves the entire routing equation, not just the low label digit.
The state word, chosen successor, sign word, and count-marker word
are unchanged. Therefore both program support masks remain Boolean.

`Znew` is strictly positive. The true zero request in row 7 contributes
`R^7`, exceeding `delta`. Nevertheless `Znew` is not Boolean: borrowing
from row 7 gives a digit two at offset `h` of row 6. The retained pair
`Znew+Dnew=H` is exact. This is the sole field whose mask is violated.

## 4. Every surviving counter guard passes

For a true zero request, the old mask fills the entire row with ones.
Rows 6 and 7 are two such consecutive rows. The exact interval
identity is

    g0*delta = sum_(j=h)^(h+m-2) 3^(6m+j).

Its support is contained in the union of those two full mask rows.
Thus subtracting it has no borrow and `Tnew` is Boolean. It removes
offsets `h,...,m-1` in row 6 and `0,...,h-2` in row 7.

At the false zero request, the numerical value is `2*3^h`. Its two
Boolean ternary tracks each have one bit, at offset `h`. Both bits
are now disjoint from `Tnew`. The source value in row 7 is zero.
Every other row has its original correct guard: true zero rows have
zero tracks, and ordinary rows have values below `R/3` and a top-only
mask. Consequently both whole words `A0+Tnew` and `A1+Tnew` are
Boolean, as are both tracks individually.

All supplied values are positive. Both tracks are nonzero already at
the initial value 54. Both sign words occur. The top mask and both
zero words are positive. The ROM junk retains count-marker bits,
and the two program support tests are positive after choosing the
width. The paid input inequality `2x<R` holds by a large margin.

The counter time identity depends only on the numerical path and its
signs, so it is unchanged. In particular the exact retained equations
include

    q=2J+1, q=Wv, W=R^3, H(R-1)=2J,
    Kp+Km=H, Znew+Dnew=H,
    6(J-Tnew)=(R-3)Dnew,
    W(A0+A1+Kp-Km)=A0+A1-2x,
    C+J=SH+TC, TV=Vnew+Zstar H,
    (RK-g)C=gI*(q-1)+R(Vnew+hs*Kp+hz*Dnew).

Here `I` is the fixed entry singleton. The checker evaluates all of
these equations on the complete ordinary integer words, as well as
the positive input slack.

## 5. The mask and full positive Pell extension

Omit only `Znew` from the packed word, retaining the eleven fields

    Kp, A0+Tnew, A0, A1+Tnew, A1, Km, Dnew, C, Vnew, TC, TV.

They are all positive Boolean words below `q`. Alternatively omit
`Dnew` as well, leaving ten such fields. For either number `f` of
fields put

    P=sum_(i=0)^(f-1) field_i*q^i,
    L=q^f, r=P+(L-1)/2, beta=L-r.

The index equation `2r+1=L+2P` and packed bound `r+beta=L` are exact.
The native word `r` has only ternary digits 1 and 2, with unit digit
2, so all `f*m*u` ternary positions carry when it is doubled. Its
central binomial coefficient has exactly that 3-adic valuation.
Thus `L` divides it. There is no initial top digit beyond the stated
length, and the final propagated carry is already the last counted
carry.

The index is even. The first six fields have parity `H`, which is
even. Here `Dold` has 169 one digits, hence `Dnew` is even; `Zold`
has five one digits, hence `Znew` is also even. The four program
fields sum to `2(C+Vnew)+J+(Zstar-S)H`, which is even. Also `J` and
`(L-1)/2` are even since `u` is even. Removing either or both of
the even zero words therefore preserves even parity.

Finally `q^(f-1)<r<L<r^2`, `L>=81`, and `r>=27`. These are the
actual general-scale hypotheses of the fixed-sign 43-operation
kernel in `EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md`. Its positive
even-index converse applies with `D0=L`, a power of three. It
constructs every positive Pell auxiliary for each malformed outer
witness. No assumption that `L` is an integer square is imported;
in particular the eleven-field scale is legitimate. Enormous Pell
coordinates are not numerically instantiated by this regression.

Thus the issue is not an unproved preliminary bound or only a local
ROM ambiguity. For this fixed empty-predicate graph, the surviving
full outer equations and the full positive kernel have a solution
at the positive input 27.

## 6. Doubling the words does not repair the obstruction

Double every raw field, `H`, and `J`, as in the doubled-coordinate
architecture. The top, pair, support, and routing equations scale
exactly. The counter input becomes `4x`, with a positive slack
`R-4x`; the chosen width satisfies this stronger bound. The retained
fields now have digits zero or two. Their packed sum is `2P`, so
the same index satisfies `2r+1=L+2P`. Every relevant parity is even,
including the malformed complementary word.

Consequently deriving that `D` is even from the ROM does not make
the omitted mask redundant. The counterexample already has that
property before doubling and has an exact doubled source transport.
This does not challenge the doubled construction with both zero
masks retained.

## 7. Verification scope

The checker builds the fixed graph and ROM constants afresh. It
checks every surviving row mask from explicit support sets, including
the dense interval removal, then evaluates the full positive integer
outer equations. Both altered field packings, their index equations,
positive slacks and general kernel bounds are evaluated exactly.
The binomial valuation follows from the exhaustively checked digit
supports and the exact native carry theorem, rather than construction
of the binomial integer. The source compiler's published 105/104
files are untouched.
