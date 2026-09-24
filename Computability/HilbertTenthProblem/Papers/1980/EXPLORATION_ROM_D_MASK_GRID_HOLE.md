# D-only omission with ordered coordinates and dense off-grid forbidding

The nozero mask can still fail after placing every zero-request state below
every other state and forbidding every off-grid position in the fixed ROM
product span. The counterexample uses a chosen destination's output column:
that column is absent from the chosen edge's junk, but must remain available
as junk for another edge from the same source.

This strengthens `EXPLORATION_ROM_D_MASK_OMISSION.md`. That earlier family
uses a freely repairable off-grid hole. Here the added bit is on the grid and
is required by a genuine alternative transition. The conclusion concerns
the stated convolution controller and fixed graph. It does not rule out a
different machine compiler, for example one that permits branching only at
zero-valued dispatch states.

The exact checker is `../verification/explore_rom_d_mask_grid_hole.py`, with
its adjacent JSON receipt. It imports the earlier counterfamily's finite
cycle controls and symbolic deltas. No frozen arithmetic certificate or
operation frontier is changed.

## 1. The fixed graph and the indispensable hole

Use the thirty-state empty graph and its sign/zero labels from Section 2 of
`EXPLORATION_ROM_D_MASK_OMISSION.md`, and add one edge

\[
 13\longrightarrow17.
\]

The selected counterexample path continues to use `13 -> 14`. Both possible
destinations have phase two, whereas state thirteen has phase one, so both
edges respect the serial three-counter phase. Every positive return to state
zero still passes the false zero request at state twelve before reaching
either edge. The graph remains honestly empty on every positive input.

Assign Sidon state coordinates with all three zero-request coordinates
strictly below the other twenty-seven state coordinates. The exact algorithm
assigns the smallest coordinates to states `1,2,12`, in that order, and then
assigns the remaining state coordinates in increasing state order. Every
coordinate and every table exponent is a multiple of four. This spacing
has explicit marker capacity `3^4=81>30`, as required by the inherited
malformed-subset count-marker theorem. The sign and
nozero port coordinates `b_s,b_z` are above all state coordinates.

Write `d` for the largest coordinate and retain the usual convolution table

\[
 K=\sum_{i\to j}3^{d+a_j-a_i}
   +\sum_i3^{d-a_i}
   +\sum_{s_i=+1}3^{d+b_s-a_i}
   +\sum_{z_i=0}3^{d+b_z-a_i}.
\]

Put

\[
 c=d+a_{14},\qquad h_z=3^{d+b_z}.
\]

In the row for edge `13 -> 14`, the coefficient at position `c` is removed
as the chosen next-state output. It is therefore absent from that row's
junk. In the row for the genuine edge `13 -> 17`, the same coefficient is
an unchosen output and remains in the junk with digit one. The companion
checks both exact rows.

This has two precise consequences within the unchanged controller:

1. A fixed forbidden mask disjoint from every correct transition's junk
   cannot contain `c`.
2. Increasing the table coefficient at `c-a_13` from one to two gives the
   correct alternative row `13 -> 17` a junk digit two, which its Boolean
   mask rejects.

Thus this hole is not removed by the earlier free off-grid repair or by
adding table mass at its already occupied coefficient while preserving both
ordinary transition witnesses. This is a local obstruction to those
repairs, not a classification of arbitrary new encodings.

## 2. Every off-grid position is already forbidden

Let `span=max(supp(K))+max_i a_i`, which bounds the entire fixed product
`K S`. Add to `Z_*` every position `p <= span` with `p mod 4 != 0`, along
with the two output ports, the count marker's three following positions, and
the usual fresh high forbidden bit. The high bit is chosen above
`KS,gS,6(h_s+h_z),3S` and the existing forbidden word. Choose `R=3^m`
strictly above `2Z_*+1,KS,gS,81`.

Every correct fixed row has Boolean junk wholly on the grid, so this dense
off-grid forbidden word preserves all thirty-six correct edge rows. The
chosen next-state column `c` is on the grid and remains allowed because the
alternative row actually uses it.

The reproducible constants in the receipt are

\[
\begin{array}{rl}
 \mathrm{span}&=29576,\\
 |\operatorname{supp}(Z_*)|&=22185,\\
 m&=29578,\\
 d+b_z&=24360,\\
 c=d+a_{14}&=19084.
\end{array}
\]

The exact row checks include positivity, the convolution identity,
disjointness from the full forbidden word, and the ordinary state support
test. None depends on enumerating the eventual enormous path.

## 3. Aligning the two-row interval repair with that column

Set

\[
 s=(d+b_z)-c=b_z-a_{14}>0,
 \qquad h=m-s,
 \qquad x=3^h,
 \qquad j=(3^{h-1}-1)/2.
\]

The actual constants give `s=5276`, `h=24302`, and `2 <= h <= m-2`.
Take exactly the prefix/pump/bad-block/cleanup path of the earlier note:
one prefix, `j` pump cycles, the bad block once, `x` counter-zero cleanup
cycles, and `j` counter-one cleanup cycles. Its false zero row and duration
are still

\[
 b=6+6j=x+3,\qquad u=12+6x+12j=8x+6.
\]

At the false zero row both ordinary numerical tracks equal `3^h`. At the
next row, state thirteen, both tracks equal `(3^{h-1}-1)/2`.

The interval identities from the earlier note hold for every
`2 <= h <= m-2`, not just for `h=m-2`. Explicitly, with
`j_R=(R-1)/2`,

\[
\begin{split}
\frac{R-3}{6}3^h
 &=\sum_{i=h}^{m-1}3^i
   +R\sum_{i=0}^{h-2}3^i,\\
j_R+\sum_{i=h}^{m-1}3^i+3^h
 &=R+\frac{3^h-1}{2},\\
\frac R3+2\frac{3^{h-1}-1}{2}+1
 &=\frac R3+3^{h-1}<R.
\end{split}
\]

Consequently the perturbation

\[
\begin{array}{ll}
 \Delta=3^hR^b,&Z=Z_{\rm old}+\Delta,\\
 D=D_{\rm old}-\Delta,&T=T_{\rm old}+(R-3)\Delta/6,\\
 V=V_{\rm old}+h_z\Delta
\end{array}
\]

leaves both complete guards Boolean through a single carry across these
two rows. It leaves `Z` positive Boolean and makes the positive `D`
non-Boolean. The pair, interval, and routing identities are unchanged.

The key alignment is now

\[
 h_z\Delta=3^cR^{b+1}.
\]

Thus the new junk bit is exactly the selected row's missing destination
column in row `b+1`, whose actual edge is `13 -> 14`. It is not an
off-grid bit. Both `V` and `V+Z_*H` remain Boolean, even with the dense
forbidden mask.

All source values remain below `R/3`, and `4x<R`, because `h <= m-2`.
The same cycle invariants prove nonnegative execution to the zero target.
The inserted alternative edge is not used by this path and does not alter
these equations.

## 4. Complete false witnesses and exact scope

The positivity and mask argument of Sections 1, 3, and 5 of the earlier
note now applies with this new fixed graph, width, and exponent `h`.
Specifically, the eleven positive retained words are

\[
 K_+,A_0+T,A_0,A_1+T,A_1,K_-,Z,C,V,T_C,T_V.
\]

They are all Boolean and below `q=R^u`. Pack them in that order into
`P`, put `L=q^11`, and set `r=P+(L-1)/2`. The packed slack is positive;
`r` has native ternary digits one and two with unit digit two. Its exact
central valuation is

\[
 v_3\binom{2r}{r}=11mu.
\]

Its parity is even for the same separate reasons as before: even `u`
makes `H,J` and the wide repunit even, the first six field values have
even sum, the new zero word has exactly four one digits, and the four
program fields have even sum. The general forty-three-operation kernel
therefore has strictly positive witnesses at scale `L`. The inequalities
`L>=81`, `r>=27`, and `r<L<r^2` hold. Doubling the raw coordinates
also gives the corresponding zero-or-two-mask counterexample.

This supplies a full positive false-witness family for D-only omission
with ordered zero coordinates and all off-grid positions already forbidden.
The unchanged graph has no honest accepting computation on this input.

The hole is unavoidable only for fixed forbidden extensions disjoint from
every correct row, and for table padding that preserves the two specified
ordinary alternative rows. A compiler that changes where branching is
allowed, changes transition semantics, or changes the mask/convolution
architecture is outside the result. In particular no assertion is made
about a machine that branches only at dedicated zero-valued dispatch rows.

## 5. Evidence

The fresh maintained regression returns
`PASS_D_ONLY_NECESSARY_GRID_HOLE_COUNTERFAMILY` and checks all thirty-six
fixed edge rows, 704 local interval cases including the actual width,
192 finite cycle controls, and four exact symbolic deltas. It also checks
that forbidding the chosen column or raising its existing table coefficient
breaks the genuine alternative row.

The actual input is `3^24302`, the false zero row is `3^24302+3`, and the
duration is `8*3^24302+6`. These numbers describe a mathematical family;
the full history and its gigantic packed/Pell integers are not materialized.
The cycle, two-row normalization, and untouched-row proofs establish their
global properties. Finite checks are supporting regressions, not a claim of
exhausting all encodings or all histories. No improved complete operation
count or universal bound is claimed.
