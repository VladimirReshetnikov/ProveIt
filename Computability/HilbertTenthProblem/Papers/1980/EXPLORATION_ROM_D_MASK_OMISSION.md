# Omitting only the nozero field: a counterfamily for the sparse ROM

The currently used sparse fixed ROM does not make the separate mask on the
nozero word `D` redundant. There is a fixed, honestly empty thirty-state
program and an explicitly defined family of positive false witnesses in
which `Z` and all ten other retained words are Boolean, every arithmetic
history and routing equation holds, and only `D` is non-Boolean.

**This is a statement about the specified sparse forbidden word.** Adding
one fixed forbidden digit, `hz/9`, blocks this family and preserves every
correct ROM row. Fixed numerals are free in the operation model. Consequently
this result neither rules out an improved fixed encoding nor establishes a
lower bound on the number of runtime operations.

The exact companion is
`../verification/explore_rom_d_mask_omission.py`, with its adjacent JSON
receipt. The actual history has exponentially many rows in its fixed ROM
width; those global integers are not materialized by the regression. The
general cycle and carry proof below supplies that part of the result.

The corrected encoding uses grid spacing `ell=4`, with explicit capacity
`3^ell=81>30`. The first published version used spacing three and omitted
this inherited malformed-subset marker-capacity requirement. Its one-head
counterexample identities were valid, but its fixed encoding was outside
that compiler contract. The constants and receipt below have been
regenerated with spacing four; the graph and carry argument are unchanged.

## 1. Interface and the tested weakening

Use the raw-coordinate equations of
`EXPLORATION_FACTORED_RAW_BLOCKS.md`, with the ordinary cyclic program
interface of `EXPLORATION_CYCLIC_ENTRY_SERIAL_COMPOSITION.md`. Write

\[
 R=3^m,\quad q=R^u,\quad W=R^3,\quad
 J=(q-1)/2,\quad H=(q-1)/(R-1).
\]

The relevant equations, before factoring the packed polynomial, are

\[
\begin{split}
 K_++K_-&=H,& Z+D&=H,\\
 6(J-T)&=(R-3)D,& B_i&=A_i+T\quad(i=0,1),\\
 W(A_0+A_1+K_+-K_-)&=A_0+A_1-2x,\\
 2x+\alpha_I&=R,\\
 T_C&=C+J-SH,&T_V&=V+Z_*H,\\
 (RK-g)C&=gI_0(q-1)+R(V+h_sK_++h_zD).
\end{split}
\]

Here `I_0` is the fixed code of program state zero, not the raw counter
input. The proposed weakening retains masks on

\[
 K_+,B_0,A_0,B_1,A_1,K_-,Z,C,V,T_C,T_V
\]

and omits only `D`. Every named supplied coordinate in the construction
below is strictly positive. In particular `D` remains a positive integer;
the defect is its digit alphabet, not its sign. The word `T` is not separately
masked. The proof checks the actual masked sums `A_i+T` and does not assume
that `T` has Boolean digits.

## 2. A fixed empty program

States are numbered from zero to twenty-nine; state `i` acts on counter
`i mod 3`. Five six-state blocks have the following signs:

| States | Signs | Effect on the three counters |
|---|---|---|
| 0--5 | `+++---` | identity |
| 6--11 | `+++-+-` | add two to counter one |
| 12--17 | `+++---` | identity |
| 18--23 | `-++---` | subtract two from counter zero |
| 24--29 | `+-+---` | subtract two from counter one |

There is an edge `i -> i+1` for each `0 <= i < 29`, and also

\[
5\to12,\quad11\to6,\quad23\to18,\quad23\to0,
\quad29\to24,\quad29\to0.
\]

The zero-request states are exactly `1,2,12`. All other states emit the
nozero label. As usual a zero request is an additional condition on the
source counter; an ordinary nozero-labelled state need not assert that its
counter is positive.

Every positive return to state zero must pass state twelve. Before that
state, the prefix and any number of pump cycles preserve counter zero at
its strictly positive initial value `2x`. Thus the zero request at state
twelve is false on every putative accepting computation. The program is
honestly empty on all positive inputs.

For `m >= 4` put

\[
 h=m-2,\qquad x=3^h=R/9,\qquad
 j=(3^{m-3}-1)/2=(x/3-1)/2.
\]

Take the prefix once, the pump block `j` times, the bad block once, the
counter-zero cleanup `x` times, and the counter-one cleanup `j` times,
then return to state zero. Ignoring only the false zero request, this is a
valid nonnegative counter path from `(2x,0,0)` to `(0,0,0)`. Its length is

\[
 u=12+6x+12j=8x+6,
\]

a positive multiple of six. The false zero row is

\[
 b=6+6j=x+3.
\]

At row `b`, the source vector is `(2x,2j,0)`. At row `b+1`, whose active
counter is counter one, the source value is
`2j=3^{h-1}-1`. Every source counter is below `R/3`: counter zero is at
most `2R/9+1`, counter one at most `R/27`, and counter two at most one.
Both the original paid input bound `2x<R` and the doubled version `4x<R`
hold.

Split each ordinary ternary source digit into two Boolean tracks by
assigning one to `A_0` when the digit is nonzero, and one to `A_1` when
the digit is two. Both tracks at row `b` equal `3^h`. Both tracks at row
`b+1` equal

\[
 a_{\rm next}=(3^{h-1}-1)/2.
\]

These tracks, the sign words, and the state word `C` are genuine words of
the path. Their numerical time identity holds by telescoping the ordinary
three-counter update equations.

## 3. A two-row change that preserves every retained interval mask

Let `Z_old` consist of the declared zero heads, including the false head
at row `b`; let `D_old=H-Z_old`, and define
`T_old=J-(R-3)D_old/6`. These words are auxiliary values for the starting
path, not a claim that its false-zero guards already pass.

Set

\[
\Delta=3^hR^b,
\qquad
\begin{array}{ll}
 Z=Z_{\rm old}+\Delta,&D=D_{\rm old}-\Delta,\\
 T=T_{\rm old}+(R-3)\Delta/6,&V=V_{\rm old}+h_z\Delta.
\end{array}
\]

The pair, interval, and routing expressions are unchanged exactly:

\[
 Z+D=H,\qquad6(J-T)=(R-3)D,
 \qquad V+h_zD=V_{\rm old}+h_zD_{\rm old}.
\]

The new `Z` is Boolean: a previously empty bit at position `h` of row
`b` is added beside that row's unit zero bit. The new `D` is positive,
since its subtraction borrows from the nozero head in row `b+1`; its
row-`b` residue is `R-3^h`, whose digit at position `h` is two. Therefore
`D` is not Boolean.

Put `j_R=(R-1)/2`. The exact split

\[
\frac{R-3}{6}3^h
 =\sum_{i=h}^{m-1}3^i
   +R\sum_{i=0}^{h-2}3^i
\]

shows that the changed `T` has two affected rows. At the false zero row,
adding either track gives

\[
 j_R+\sum_{i=h}^{m-1}3^i+3^h
   =R+\frac{3^h-1}{2}.
\]

Its normalized row is Boolean and it emits a carry of one. At the next
row, the existing top marker, the changed spill, the actual track, and
this incoming carry give

\[
 \frac R3+2\frac{3^{h-1}-1}{2}+1
   =\frac R3+3^{h-1}<R.
\]

This row is also Boolean and emits no carry. Every other row has an
ordinary correct top or true-zero interval. Consequently both complete
words `A_0+T` and `A_1+T` are Boolean. This explicitly exhibits why the
unmasked `T` cannot be treated as a Boolean word. Since `A_i>0` and each
complete guard is at most `J`, the whole positive value `T` is less than
`J`, even though its local coefficients used a carry.

## 4. The exact sparse ROM and its unused column

The checker specifies the fixed constants reproducibly. It greedily
chooses thirty-two integers with distinct unordered pair sums, translates
them to an interval whose minimum is more than half its maximum, and
multiplies every coordinate by four. Thirty coordinates represent states;
the last two are the sign and nozero output coordinates. Write them as
`a_i,b_s,b_z`, and put `d=max(a_i,b_s,b_z)`.

The monomial exponents of `K` are

\[
\begin{split}
 d+a_v-a_u&\quad\text{for program edges }u\to v,\\
 d-a_i&\quad\text{for every state},\\
 d+b_s-a_i&\quad\text{for positive-sign states},\\
 d+b_z-a_i&\quad\text{for nozero states}.
\end{split}
\]

Their digits are all one, their exponents are distinct, and every exponent
is a multiple of four. The spacing is large enough that the marker block
can represent every subset cardinality: `3^4=81>30`. Set

\[
 S=\sum_i3^{a_i},\quad g=3^d,
 \quad h_s=3^{d+b_s},\quad h_z=3^{d+b_z}.
\]

The current forbidden positions are `d+1,d+2,d+3,d+b_s,d+b_z` and one fresh
high position `e`. The checker chooses `3^e` above
`KS,gS,6(h_s+h_z),3S` and the preceding forbidden word, then chooses
`R` strictly above `2Z_*+1,KS,gS,81`.

For this thirty-state graph the exact returned values are

\[
 m=29606,\qquad
 \operatorname{supp}(Z_*)=\{12181,12182,12183,23848,24360,29605\}.
\]

All thirty-five edge rows are checked exactly. Their ordinary junk words
are positive Boolean words below `R`, disjoint from these forbidden
positions. Every ordinary junk exponent is a multiple of four.

The perturbation in the preceding section adds to the complete junk word

\[
 h_z\Delta=(h_z/9)R^{b+1}.
\]

Its within-row exponent is `24358=24360-2`. This is not a multiple of
four, so it is absent from every ordinary junk row. It is also absent
from the current forbidden word, and is below `m`. Thus `V` is Boolean,
and `T_V=V+Z_*H` is Boolean. The state-support word remains
`T_C=C+J-SH`, also positive Boolean, because each state row is one-hot in
`S`. The routing equation is still exact by the invariant `V+h_zD`.

The chosen width is fixed by the fixed graph. Its corresponding input and
path are enormous but finite:

\[
 x=3^{29604},\qquad b=3^{29604}+3,
 \qquad u=8\cdot3^{29604}+6.
\]

## 5. Positivity, the complete weakened mask, and the Pell extension

The initial source value `2x` makes both track words positive. Both signs
occur. The explicit zero heads make `Z` positive; the many other heads
and the single next-row borrow leave `D` positive. The interval word is
positive and its guards are positive. Every ordinary ROM junk row is
positive, and both support tests are positive. The geometric and input
slacks are positive, and `q=Wv` has a positive integer quotient because
`u` is a multiple of three.

Pack the eleven retained fields, in the order in Section 1, into

\[
 P=\sum_{i=0}^{10}F_iq^i,\qquad L=q^{11},
 \qquad r=P+\frac{L-1}{2}.
\]

Every `F_i` is a positive Boolean ternary word below `q`. Not every
retained digit is one, since `C` is sparse. Thus
`0<P<(L-1)/2`, and the packed slack `L-r` is positive. The first sign is
positive, so `r` has unit digit two. All its higher digits below `L` are
one or two. Doubling `r` has exactly `11mu` ternary carries, and hence

\[
 v_3\binom{2r}{r}=11mu,\qquad L\mid\binom{2r}{r}.
\]

The index is even. Indeed, `u` is even, so both `H` and `J` are even.
The first six fields have sum
`H+2(A_0+A_1+T)`, which is even. The new `Z` has four one digits. The
four program fields have sum
`2(C+V)+J+(Z_*-S)H`, which is even. The wide repunit `(L-1)/2` is even
as well. Since `q` is odd, these sum parities prove that `r` is even.

Apply the positive fixed-sign forty-three-operation kernel converse from
`EXPLORATION_UNIT_TWO_TERNARY_KERNEL.md` at the actual scale `D_0=L`.
Here `L>=81`, `r>=27`, `r<L<r^2`, and the required central divisibility
and even parity have just been proved. All its remaining witnesses exist
and are strictly positive. This is a complete positive extension of the
weakened outer system; no gigantic Pell integer is asserted to have been
materialized by the regression.

The same counterexample also has a doubled-coordinate version. Double
the raw fields, `J,H,T`, and the raw history input load. Every retained
field then has digits zero or two; the packed link uses their undivided
sum, so the same `r` and kernel witnesses apply. The malformed `D` is
even but is still not a zero-or-two word. In particular routing parity
alone does not recover its missing mask.

## 6. The free repair and the unresolved stronger encoding

Add `h_z/9=3^24358` to the fixed forbidden word. No arithmetic instruction
is added. That position is absent from every correct ROM row, so all
canonical witnesses remain available after sufficiently widening `R`.
The altered junk row of this counterfamily now has digit two in its
support test and is rejected.

The demonstrated failure therefore belongs to the existing sparse
forbidden mask. Filling all non-grid positions in the fixed ROM span is
also a free encoding change. Whether D-only omission can be made sound
by such a strengthened encoding, possibly with additional fixed padding
at allowable grid positions, is unresolved by this example.

## 7. Reproducible evidence boundary

The maintained checker establishes:

* all thirty-five fixed ROM edge identities and support conditions;
* the actual-width two-row interval identities, plus sixty-one smaller
  width controls;
* 192 finite pump/cleanup controls;
* four exact symbolic perturbation identities;
* the exact off-grid junk position and its absence from all correct rows.

The receipt records sixty-two local interval cases in total. The cycle
invariants prove the specified enormous history; the two-row calculation
and untouched-row argument prove its complete masks. The full kernel
extension uses the cited general converse. These general mathematical
claims are distinct from finite regression counts. No complete optimized
schedule for the unsound omission, no smaller universal bound, and no
encoding-independent omission theorem is claimed.
