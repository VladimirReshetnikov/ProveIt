# Five countdown registers remove the external Pell-input interface

The directed193 membership family has an exact **five-register affine transition representation with ordinary input copied directly**. Four signed registers track the two matrix rows; a fifth counts down from the supplied integer x. There are97 transition choices: one loader and the96 synchronized tile transitions. No phase register, switch transition, supplied Pell coordinates or separate exact-index condition remains.

For the actual saved context-absorbed fixture, the complete local polynomial has **2065=1115M+950A** operations and exact degree194. Initializing the input costs zero gates, and the full endpoint predicate costs **7=3M+4A**. These are local costs. Encoding arbitrarily many transitions with a fixed number of Diophantine witnesses remains unpaid, so this is not an improvement to the complete universal84-operation bound.

## 1. Fixed matrices and the ordinary-input interface

Use the [synchronized-row source](matrix193_synchronized_rows.md), reconstructed from the actual [context-absorbed193 array](matrix193_context_absorption.md). For every retained tile i it gives fixed matrices

    K_i=C^(-1) H_i C, G_i,

where the upper blocks of A_i, B_i and the central generator are H_i, G_i^(-1) and C. Let B be the fixed repeated even block. All these matrices and B lie in the inherited group H'; all are integral with determinant one. In the saved fixture,

    B=[[-52109,29036],[-94920,52891]],
    B^(-1)=[[52891,-29036],[94920,-52109]],
    e1 C=(35426321,-19628667).

A state is `(X0,X1,Y0,Y1,n)`, with two row vectors X,Y and a signed counter n. Start at

    X=e1 C, Y=e1=(1,0), n=x.                           (1)

Every initial entry is a fixed numeral or the direct input wire x. The transition choices are:

    LOAD: X'=X, Y'=Y B^(-1), n'=n-1;
    TILE_i: X'=X K_i, Y'=Y G_i, n=n'=0.               (2)

The target condition is

    X=Y, n=0.                                         (3)

The equations do not impose nonnegativity on state witnesses. The counter argument below works with signed counters, so there is no hidden inequality or uncharged phase guard.

## 2. Why the countdown forces the exact input exponent

On every LOAD step the counter decreases by one. A tile step leaves it zero. Thus a finite path from counter x to counter zero has exactly x LOAD steps. In particular such a path can exist only for a nonnegative integer x.

If a tile occurs, its current counter is zero, so by that point exactly x loads have already occurred. No further load is possible on a path ending at zero: it would make the total load count greater than x. Consequently every accepting transition word has exactly the shape

    LOAD^x TILE_(i1)...TILE_(id), d>=0.                (4)

This establishes the order as well as the count. It does not assume a positive counter domain. In particular a locally legal load from zero to -1 cannot belong to an accepting path. The loader and tile branches are disjoint even at counter zero, since their required next counters differ.

After the prefix in(4), X=e1 C and Y=e1 B^(-x). The row theorem therefore gives

    a finite path from(1) to(3)
      iff diag(B^(-x),P) belongs to the fixed193 semigroup. (5)

For completeness, the tile path yields rows `e1 H(s) C` and `e1 B^(-x) G(s)`. Both underlying matrices lie in H'. Equality of the rows is therefore full matrix equality by the inherited first-row theorem. Its rearrangement is precisely the upper block of `A_s C B_reverse(s)`; the lower block is P. Conversely every old positive product with lower block P has this shape and supplies the tile suffix. The case d=0 corresponds to the single old generator C, not to an empty semigroup product.

Together with the inherited fixed-program initialization and context transfer, (5) preserves the ordinary positive-integer language for every program-specific alphabet supplied by that theorem. The matrices in (2) depend on the program's fixed contexts; they do not depend on the varying x. This is an effective fixed-program transition recipe, not a claim that the particular illustrative contexts `[110` and `A0]` initialize every c.e. language. No arbitrary-program compiler was executed in this packet.

The counter construction enforces the literal number of applications of B^(-1). It requires neither a Pell norm nor an independently supplied index, and it does not identify an arbitrary Pell solution with the intended input. Compared with [the counted-suffix matrix lift](matrix195_counted_suffix.md), this uses its original four row coordinates and one scalar counter rather than a seven-dimensional matrix-product history. It is a different certificate interface, not an asserted end-to-end operation saving between completed Diophantine constructions.

## 3. Complete local polynomial and paid source

Let P_step(X,Y,X',Y') be the parent's full degree192 polynomial for the96 tile choices. It is a product of sums of four squares, hence nonnegative on all real coordinates. Let

    E_load = (X0'-X0)^2 + (X1'-X1)^2
           + (Y0'-(Y B^(-1))0)^2 + (Y1'-(Y B^(-1))1)^2
           + (n-n'-1)^2,
    E_tile = P_step + n^2 + (n')^2,
    P_count = E_load E_tile.                           (6)

Every factor in(6) is nonnegative on real coordinates. Therefore P_count=0 holds exactly on one of the97 transitions in(2), over the integers or the reals. Adding the counter squares to the entire nonnegative P_step safely shares its guard across all96 tile choices. The construction does not expand the guard separately into96 branches.

The saved full source retains all2039 parent instructions literally, then adds26 live instructions:

| Added expression | M | A |
|---|---:|---:|
| Five loader residuals and their full sum of squares |9|12|
| Two counter squares and their sum with P_step |2|2|
| Final product |1|0|
| Added total |12|14|

Thus the actual full local source costs2065=1115M+950A. Every multiplication by a fixed coefficient of B^(-1) is paid. It has ten supplied signed state ports, no auxiliary selector, phase or Pell coordinate, and all instructions are live.

Degree194 is exact in these ten independent ports, with all fixed matrix coefficients counted as degree-zero numerals. The source-degree upper bound is194. On the line where only `next_X0=t` is nonzero, each parent branch contributes t², so P_step=t^192, E_tile=t^192 and E_load=t²+1. Hence

    P_count=t^194+t^192.

Its nonzero coefficient1 certifies attainment without zero-only substitutions. The helper verifies this complete univariate specialization on the literal DAG. It separately interprets the added source over a formal independent port for the entire parent output and compares the exact grouped polynomial with(6).

The full endpoint polynomial is

    (X0-Y0)^2+(X1-Y1)^2+n^2,

with all seven gates saved and evaluated. The initial source is empty: four fixed constants and one copy of x. There is no varying target arithmetic or external indexing obligation hidden in that zero-gate count.

The2065 ledger concerns this actual fixed-context fixture and its retained shared source. For arbitrary program contexts, a simple uniform schedule without cross-branch sharing costs at most2303 gates for the96 tile union: each branch uses12M+11A, followed by95 product multiplications. Adding the same26-gate countdown gives the explicit generic upper bound2329=1259M+1070A. Accidental coefficient equalities are not assumed uniformly across programs.

## 4. Fixed duration is paid; bounded-variable unbounded packing is not

For a fixed total duration h, introduce the five signed state coordinates at times1 through h, substitute(1), and sum the h instances of P_count and the endpoint polynomial. Their nonnegativity makes that sum zero exactly when every transition and the endpoint are correct. Copying the actual declared schedules gives the upper bound

    2065h + 7 + h = 2066h+7

with5h signed witnesses, zero initial-input gates and degree at most194 for h>=1. This is an explicit finite-length compiler. Its upper degree, after the initial substitutions, is not claimed to attain194 in every specialized case. Without sharing across arbitrary program coefficients, the analogous uniform bound is2330h+7.

For integer x, any real zero trajectory also consists of integers: its initial state is integral, each local zero chooses one of the fixed integral affine transitions, and induction applies. This finite-duration exactness does not convert an unbounded family of durations into a fixed-arity polynomial.

A complete bounded-variable certificate must still encode the arbitrary-length trajectory and enforce all local choices, chronology, signed-value bounds and endpoint constraints in that encoding. Simply existentially naming h does not supply those conditions or fix the growing number of witnesses. Conversion to positive witness coordinates and all corresponding packed-history arithmetic are not charged here. No universal84 improvement follows from five registers,97 choices or the zero-gate input wire.

## 5. Genuine positive-input fixtures and replay

The pinned counted-suffix receipt supplies four accepted tile words for the same actual fixed contexts. This helper independently reconstructs the synchronized pairs from the context193 matrices, runs every countdown and tile update, and compares both rows with separately accumulated full2-by-2 products at every tile step. The complete endpoint matrix identity is checked, not just the counter.

| Ordinary x | LOAD steps | Tile steps | Total state transitions |
|---:|---:|---:|---:|
|0|0|83|83|
|1|1|843|844|
|2|2|2371|2373|
|3|3|4667|4670|

The positive inputs1,2,3 are genuine accepted finite-blank-tape inputs from the pinned machine/word construction. The x=0 case is an additional boundary fixture. The exact tile sequences and a digest of every reconstructed signed state are saved; the digest uses explicit signed, length-delimited integer bytes, not truncated decimal strings. The largest row magnitude in these traces has6424 bits. No Pell coordinates are materialized or supplied.

Bounded evidence includes all7,970 actual state transitions, all96 tile branches plus four signed loader fixtures,11 selected full-source evaluations on actual transitions,16 whole signed/rational evaluations including six rational ones, and14,329 abstract signed-counter words. The latter exactly agree with the language `LOAD^x TILE*`, including negative initial-counter rejection. Every added polynomial term is independently compared over the formal parent-output port; all62 resulting coefficients agree. The arbitrary-length proof is Section2, not extrapolation from this finite enumeration.

Full degree194 evaluation is deliberately limited on large actual traces. All affine identities and full matrix inductions are checked for every step, while the exact polynomial identity proves that those local branches are zeros at every magnitude. This avoids repeated expansion of huge off-branch products without weakening the stated proof.

The helper pins the full synchronized-row trio, the counted-suffix trio, and the context-absorption receipt/proof as inert files. It imports or executes none of their Python. The CLI rejects duplicate/nonfinite JSON, authenticates byte hashes and parent self-hashes, and compares receipts recursively with exact types. With all dependencies installed:

    python3 /absolute/path/matrix193_countdown_rows.py \
      --root /absolute/path/native-stream-queue \
      --expect /absolute/path/matrix193_countdown_rows.json

During isolated staging, `--new-root DIRECTORY` locates the two newer pinned predecessor trios separately; its default is the supplied research root. The mutually exclusive `--output FILE` writes the deterministic receipt. Writer and fresh normal and optimized exact replays from `/` passed on the frozen source and receipt. No repository or frozen predecessor file is modified.
