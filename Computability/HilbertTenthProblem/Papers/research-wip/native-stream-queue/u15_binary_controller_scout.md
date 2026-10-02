# An exact scalar U15 controller in 112 operations

The actual 29-rule U15 table admits a complete scalar transition polynomial
with **112 = 46M + 66A**, **four integer witnesses**, and **exact degree 10**.
Every integer zero represents one of those 29 transitions. The direct positive
coordinate version costs **121 = 46M + 75A**, with four positive witnesses.
These are single-step relations. Unrolling them introduces witnesses and
operations proportional to runtime; this is not a fixed universal polynomial
or a new global operation bound.

A separately emitted, grouped natural one-hot29 implementation of the same
transition relation costs **142 = 32M + 110A**, has 29 witnesses, and degree 2.
Its positive version costs **147 = 32M + 115A**. Thus the particular binary
controller saves 30 natural/integer operations or 26 positive operations,
while increasing degree and the multiplication count. The one-hot comparator
shares state groups, groups equal output coefficients, performs common
subexpression elimination, and removes dead gates. Neither implementation is
claimed optimal.

## Exact source table and coding

The source is the local `neary_woods_explicit_universal_tm.py`, SHA256
`0a0f970df8dcf4dca5f8d105908b06f82fefb3e1948198ca2692fcb97b5da0e5`.
The checker reads its literal `TABLES` assignment through Python AST after
verifying its hash; it does not execute that module. Its 29 rules equal the
separate table transcription in this scout. The earlier complete Waterfall
frontend review checked the published Table 16 and the unique missing J/b
instruction against the primary paper; the scalar analysis here uses that
same table. Read/write 0 means c, 1 means b, and the output `left` is 1 for L.
The primary table is in [Neary–Woods, *Four small universal Turing machines*](https://dna.hamilton.ie/assets/dw/NearyWoods-FI09.pdf).

| State | Code | Read 0 | Read 1 |
|---|---:|---|---|
| A |0|0RB|1RA|
| B |15|1RC|1RA|
| C |14|0LG|0LE|
| D |1|0LF|1LE|
| E |4|1RA|1LD|
| F |12|1LD|1LD|
| G |9|0LH|1LG|
| H |13|1LI|1LG|
| I |6|0RA|1LJ|
| J |5|1LK|halt|
| K |2|0RL|1RN|
| L |11|0RM|1RL|
| M |8|0LB|1RL|
| N |10|0LC|0RO|
| O |3|0RN|1RN|

The unused four-bit code is 7. The initial state A retains code 0 and the
halting state J has code 5. Thus a packed state transport using this coding
would have terminal coefficient 5 and no initial state offset. This statement
about the transport constants does not itself supply a packed controller.

## Complete integer zero-set theorem

The five free coordinates are current state `q`, read bit `s`, next state
`n`, written bit `w`, and direction bit `d`. Supply four integer witnesses
`b0,b1,b2,b3` and put `b4=s`. Let

    C = b0 + 2 b1 + 4 b2 + 8 b3.

A shared Shannon arithmetic DAG evaluates three multilinear polynomials
`f,g,h` of the five bits. On every defined table row they return respectively
the next-state code, write bit, and direction. Every mux is the exact integer
polynomial `lo + x*(hi-lo)`, with literal constant/zero/one simplifications and
shared gates. A branch containing no defined row may use its sibling's value;
this affects only the three forbidden inputs. Induction through the recursion
proves every defined row is preserved. The complete lookup uses 76 operations,
of which 20 multiplications have two nonconstant operands.

Because unused code 7 and J code 5 share `b0=1,b2=1,b3=0`, define

    G = b0*b2*(1-b3) * (b1 + (1-b1)*s).

On Boolean inputs this is 1 exactly for unused state 7 (either read bit) or
for J/read1. It is 0 on all 29 defined rows. The emitted polynomial is

    F = (C-q)^2 + (f-n)^2 + (g-w)^2 + (h-d)^2 + G^2
        + sum(i=0..4) bi*(bi-1).

For every integer `z`, `z*(z-1)>=0`, with equality exactly at 0 and 1.
Every displayed summand is therefore nonnegative on the **full integer
orthant**, including negative coordinates. A zero forces all five bits,
the state binding, the three table outputs, and the forbidden-input guard.
Conversely each defined transition has the unique four-bit state witness
and makes F zero. Thus the complete integer zero set projects bijectively
onto the 29-row scalar transition graph; it is not merely a Boolean-input
lookup test. No separate output typing is needed because the exact table
outputs already supply it.

The implementation shares `1-bi` with the lookup/guard and subtracts
`bi*(1-bi)` when assembling F. This is the exact polynomial above on arbitrary
integer assignments. Every emitted instruction is an ordinary scalar binary
addition, subtraction or multiplication, including multiplication by fixed
coefficients. All 112 source instructions are live.

To obtain the positive-coordinate relation, replace all nine coordinates
(the five free coordinates and four witnesses) by their positive hats minus
one. The literal source emits all nine subtractions. This gives 121 gates
and an exact off-zero substitution identity, not only a zero-set implication.
Every admissible bit hat is 1 or 2. In the positive parameter interface the
initial and halting state hats are 1 and 6 respectively.

Exact sparse expansion gives 297 terms for F and 317 for its positive
substitution. Their leading homogeneous part is exactly

    197 * b0^2*b1^2*b2^2*b3^2*s^2,

or the corresponding degree-ten hatted monomial. This establishes exact
degree 10 without relying on loose DAG degree propagation.

## The one-hot comparison

For every actual rule i introduce a natural selector `ei`. The six equations
are `sum ei=1` and equality of the five free coordinates to the corresponding
weighted sums of source-state code, read bit, next-state code, write bit and
direction. Since the selectors are natural, the checksum itself forces exactly
one selector to be 1; no redundant selector Boolean equations are charged.
The comparator squares these six residuals and sums them.

The source-state groups and their checksum share the same sums. The next-state
projection groups all edges with the same target. The Boolean projections
reuse complete source-state groups when both outgoing edges have the same
column value. Exact instruction CSE and dead-gate elimination finish the
literal 142-gate source. This baseline theorem is natural-domain; arbitrary
signed selectors are not asserted to form a one-hot vector.

For positive selectors replace `ei` by `ehat_i-1` inside the affine equations.
The implementation groups the hatted selectors directly, uses checksum 30,
and pays each changed affine constant. It does not need 29 separate selector
decode subtractions. All five free parameters are also shifted to hats. This
produces the 147-gate comparator. The direct witness bijection sends a selected
rule to its four state bits; the inverse selects the unique table row determined
by the typed state and read bit. No identity between the binary and one-hot
polynomials away from their zeros is claimed.

## Evidence and reproducibility

Run, using the research environment with SymPy:

    python u15_binary_controller_scout.py \
      --root /path/to/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue

The portable function is `verify(wip_root)`. The checker writes nothing in its
default mode and compares the adjacent receipt. `--write` explicitly refreshes
that receipt. Python assertions must remain enabled. It has no permanent
`/tmp` import dependency and only the explicitly supplied source root is read.

The receipt contains all four complete arithmetic sources and ledgers, exact
polynomial expansion hashes and leading coefficients, and these checks:

- 29 rules matched to the pinned actual compiler table;
- all 2,048 five-bit input / typed-output combinations, exactly 29 zeros;
- all positive-coordinate substitutions of those 2,048 tuples;
- 232 wrong-state or wrong-output adversaries;
- 7,776 signed bit tuples in `[-2,3]^5`, with all four interfaces deliberately
  satisfied by the emitted lookup; exactly the 29 valid Boolean tuples survive;
- all 29 natural and positive one-hot witnesses;
- 306 exact-type/canonical-packet rejections, including float coefficients,
  Boolean coordinates, and source-container changes;
- exact symbolic equality of the positive substitution and the integer source,
  and live-gate checks for all four sources.

The encoding was found by a bounded heuristic over state permutations and
shared Shannon orders. The default verifier replays the final exact result,
not a time-dependent search. No minimality claim follows from that search.

The writer and fresh read-only replay both passed. Root review checked the
complete emitted sources, the integer nonnegativity theorem, the forbidden
input guard and the exact degree calculation. The maintained packet preserves
the final deterministic result rather than its heuristic search history.

## Packed-history limitation and next transfer target

The 112 count is scalar. In particular, substituting packed words into its
ordinary multiplications does not evaluate the transition separately at each
time. Already `(1+B)*(1+B)=1+2B+B^2`, whereas the coefficientwise Boolean
product is `1+B`. Increasing B cannot remove the convolution cross terms.

The existing complete prescribed-scale native AND64 can implement genuine
full-cell selected products using `(B-1)*selector` masks, given a paid dyadic
cell geometry, canonical lane bounds and Boolean selectors. The current
lookup has 20 nonconstant multiplications; several multiply a bit by a signed
difference of branch values. A packed translation must replace these by
proved selections or another complete local-relation compiler, charge the
lane assembly and range proofs, and pay the final constraints. Assigning a
free lookup cost of 76 or 112 to a packed word is invalid.

The reviewed native Boolean-selector and cyclic NAND components also retain
specified positive truth-prefix, length and wiring restrictions. They cannot
be inserted as unconstrained per-time circuit gates merely because they
implement Boolean operations. Likewise the U9 control-quotient/tag compiler
proves a complete simulation and paid input loader, but provides no free
packed arithmetic lookup for this U15 table.

Consequently the immediate certified saving is a complete **single-step**
component and fewer scalar witnesses. Its transfer into root's separate
fixed-arity packed two-tape compiler remains additional work.
