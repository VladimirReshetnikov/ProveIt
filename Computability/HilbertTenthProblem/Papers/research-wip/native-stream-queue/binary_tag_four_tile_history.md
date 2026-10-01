# Four continuing tiles for binary tag halting

A fixed binary tag system of the form

\[
 b\longmapsto b,\qquad c\longmapsto u,
\]

with deletion number `beta>=2` and nonempty `u` ending in `b`, has an
exact four-tile generalized correspondence representation of halting on
the input slices described below. The terminal condition is a fixed
suffix, not a fifth selectable tile. Every matching sequence implies
halting, and every computation reaching the singleton `b` gives a match.
For inputs ending in `b` with `|w|=|u|=1 mod(beta-1)`, these implications
give equivalence. No restriction forbidding adjacent `c` symbols is needed.

The actual three-slope-class history gives a **195-operation**, degree
**666** positive polynomial for a nonempty matching tile word. Including
the initially halted singleton gives **197 operations**, degree **667**,
with **28 positive witnesses**. These are exact counts for the four
literal examples in the receipt, and a uniform upper bound using the
same paid schedule for the nontrivial production family. The input to
this predicate is the ordinary positive integer sentinel of the encoded
tag word. A compiler from arbitrary recursively enumerable sets to these
integer inputs is **not** included: this is not a new universal 75/87
bound, nor an instantiated universal tag program.

The construction adapts the local simulation in Neary's published
[STACS 2015 paper, Section 4](https://drops.dagstuhl.de/storage/00lipics/lipics-vol030-stacs2015/LIPIcs.STACS.2015.649/LIPIcs.STACS.2015.649.pdf).
That paper gives five-pair PCP instances by incorporating the input into
a production and using a selectable terminal pair. Its Section 3
binary-tag simulation has fixed-block data encodings; the halting
modification used for the PCP theorem also inserts the input into its
rule. These facts alone do not provide a fixed-rule ordinary-integer
universal input bridge. Here the initial data and terminal suffix are
external boundaries, and the following proof establishes the resulting
four-tile contract directly.

## 1. The exact word equation

Fix `beta>=2` and write

\[
 e(b)=10^\beta1,\qquad e(c)=1,
 \qquad E(w)=e(w_0\cdots w_{n-2})10^\beta
 \quad(w_{n-1}=b).
\]

The morphism `e` is injective. Reading a `1` followed by `0` requires
the complete block `10^beta1`; otherwise the next letter is `c`.
This deterministic decoder consumes every image word. In particular,
`E(w)1=e(w)`.

Let `u` be nonempty and end in `b`, and put `u^-` for `u` without that
last symbol. The four selectable pairs are

| Tile | Upper word | Lower word | Intended role |
|---|---|---|---|
|`P_c`|`1`|`1 e(u^-) 10`|Apply the `c` production|
|`P_b`|`10^beta1`|`110`|Apply the `b` production|
|`D_b`|`10^beta1`|`0`|Delete another `b`|
|`D_c`|`1`|`0`|Delete another `c`|

For a tile word `s`, let `h(s),g(s)` be its two concatenated images.
The boundary equation is

\[
                   h(s)10^\beta=E(w)g(s).                 \tag{1}
\]

An empty tile word solves (1) exactly when `w=b`.

## 2. Every solution has the correct deletion phases

Every maximal zero run in the left side of (1) has length exactly
`beta`. This includes its final run. The right side initially ends in
`beta` zeros. Each production tile starts its lower word with `1`, has
only internal zero runs of length `beta`, and ends in one zero. Each
deletion tile contributes one zero.

Consequently the first tile, if any, must be a production: an initial
deletion would extend the initial run beyond `beta`. After a production,
exactly `beta-1` deletion tiles must occur before the next production or
the endpoint. Too few close a shorter zero run; too many produce a
longer run. This argument concerns the completed word equality and does
not assume a valid computation prefix. Every solution therefore has
the form

\[
             (\{P_b,P_c\}\{D_b,D_c\}^{\beta-1})^T.       \tag{2}
\]

For block `i`, let `d_i` be the `beta` letters encoded by its upper
tiles, and let `v_i=b` or `u` according to its first tile. The block's
lower image is exactly `1E(v_i)`. Append one `1` to both sides of (1).
Using `E(v)1=e(v)` and injectivity, the equation is equivalent to

\[
          d_1d_2\cdots d_T b=w v_1v_2\cdots v_T.          \tag{3}
\]

As long as the current tag word has at least `beta` letters, its first
`beta` letters must be `d_i`, by (3). Its first letter selects exactly
the production `v_i`; canceling these letters leaves (3) for the next
tag configuration. Thus either the actual system halts before all
blocks are consumed, or the final configuration is `b`. In either case
it halts. This deals with short queues without pretending that a tag
transition can read symbols appended during that same transition.

Conversely, a genuine transition at a word of length at least `beta`
is represented by its production tile followed by the `beta-1`
appropriate deletion tiles. Concatenating such blocks along a
computation ending in `b` proves (3), and hence (1).

For the full halting equivalence assume also

\[
        |w|\equiv|u|\equiv1\pmod{\beta-1}.               \tag{4}
\]

Each transition preserves this length residue and produces a nonempty
word ending in `b`. A halted word has length between one and `beta-1`;
(4) forces length one, so it is `b`. We have proved

\[
 w\text{ halts}\quad\Longleftrightarrow\quad
 \exists s\text{ satisfying (1)}.                       \tag{5}
\]

The length condition is substantive: for `beta=3`, the input `bb`
already halts but cannot satisfy (1) when `|u|` is odd. Indeed the two
sides of (3) would have opposite parities.
This is a proof of nonexistence, not a bounded-search conclusion.
Without (4), a match need not describe a legal trace all the way to `b`:
at `beta=3,u=cb,w=cb`, the tiles `P_c,D_b,D_c` match, although `cb`
already halts at length two. The soundness proof deliberately stops at
the first short queue, so its conclusion remains correct.

## 3. A complete paid integer predicate

For a binary word `v`, define its positive sentinel

\[
                    [v]=2^{|v|}+\operatorname{value}_2(v).
\]

For each of the four pairs `(a_i,b_i)` above compile the fixed affine
maps

\[
 (U,V)\mapsto
 (2^{|a_i|}U+\operatorname{value}_2(a_i),
  2^{|b_i|}V+\operatorname{value}_2(b_i)).
\]

Start at `(1,x)`. On the slice `x=[E(w)]`, a common tile word gives
`U=[h(s)]`, `V=[E(w)g(s)]`. Thus (1) is exactly

\[
                     V=2^{\beta+1}U+2^\beta.             \tag{6}
\]

Supply positive `Ufinal`, compute the right side of (6) with **one
multiplication and one addition**, and substitute it for `Vfinal`
in the [complete affine history](pcp_affine_slope_class_history.md).
It is strictly positive on every positive supplied tuple, before
using any equation. This substitution therefore gives an exact positive
coordinate projection, retaining every native, range, duration and
selected-product obligation. It is not a free endpoint comparison.

The history uses baseline slopes `(2,2)`. There is one exceptional
upper slope class and two exceptional lower classes, hence `s=4`,
`g=3`, `N=s+g+4=11`. The actual factored schedule costs
`161=77M+84A`. For `|u|>=2` this fixed schedule is an upper bound;
coincident special coefficients may permit further aliases. The
source's planner retains its ordinary alternatives and chooses the
cheapest actual schedule.

For the uniform bound, write `A=2^(beta+2)`, `a=2^(beta+1)+1`,
and let `C,d` be the lower slope and offset of `P_c`. The two transport
linear forms, in positive shifted selector/selected-word coordinates,
are

    2 H_U + (A-2) ZUhat + (Shat_Pc+Shat_Dc)
          + a(Shat_Pb+Shat_Db) - fixed_constant;
    2 H_V + (C-2) ZVhat_Pc + d Shat_Pc
          + 6(ZVhat_Pb+Shat_Pb) - fixed_constant.

The upper selector group is already computed for its shared slope mask.
These give the same fixed-length grouped schedule for every `|u|>=2`;
only its fixed numerals change. This supplies the 161 bound independently
of finite example sampling. Coincidences can reduce the actual count.

The [positive native-unit projection](pcp_uniform_affine_pair_units.md)
adds three multiplications and removes nine comparisons and six
witnesses. Including the paid endpoint above gives

| Stage | Operations | Equations | Positive witnesses |
|---|---:|---:|---:|
|Raw fixed history|161 = 77M + 84A|19|33|
|Computed endpoint and native units|166 = 81M + 85A|10|28|
|Single integer-product polynomial|**195 = 91M + 104A**|one polynomial|28|

The last polynomial, called `F`, recognizes a nonempty tile word.
To include the empty word, multiply it by

\[
                     x-[E(b)]=x-3\,2^\beta.              \tag{7}
\]

The literal subtraction and multiplication add two operations. Thus
`F*(x-3*2^beta)` has **197=92M+105A** operations and the same 28 positive
witnesses. The numeral `3*2^beta` is fixed compiler data. At that
singleton input any positive witness tuple suffices; otherwise the
equation forces `F=0`. This finalizer is a disjunction with one fixed
input, not a deletion of a positivity condition.

The endpoint substitution is affine and has a positive leading form.
It leaves `deg P=2`, `deg q_native=2N`, and the native highest-form
argument unchanged. The four norm/checksum factor degrees are
`117,260,71,22`; the unique largest outer residual degree is `98`.
Their product with the positive outer sum gives
`117+260+71+22+2*98=666`. The nonzero linear factor (7) raises this
to exactly **667**. The checker verifies the exact leading coefficients
on the actual substituted DAG.

## 4. What remains before a universal ordinary-input bound

The integer `x` in Section 3 is supplied directly. No recoding of `x`
is hidden inside the 195/197 counts. Conversely, the assertion that a
particular `x` equals `[E(w)]` for a semidecider's input encoding is not
proved by that predicate. The theorem describes its exact behavior on
the specified word slices and its complete GPCP interpretation on all
positive integers.

An equal-content pair of fixed tag input blocks has equal encoded
length under `e`. Such a block morphism can use the repository's paid
bit recoder and affine program frame. This is a potential next input
interface, not a proof that every r.e. language already has such a slice.
The known clockwise-TM-to-cyclic-tag initialization also uses a
power-of-two tape-length counter; that additional input relation must
be paid or eliminated. Likewise the published binary-tag halting
construction's input-bearing production cannot silently become a fixed
rule. Neither interface is asserted complete here.

## 5. Executable evidence

```sh
/tmp/diophantine-research-venv/bin/python binary_tag_four_tile_history.py
```

The [checker](binary_tag_four_tile_history.py) and
[receipt](binary_tag_four_tile_history.json) include the four literal
tag programs, every scalar gate of one complete polynomial, their
actual alternative history ledgers, exact degree audit, arbitrary signed
native-unit identities, independent sentinel/affine equalities, halting
trace encodings, and exhaustive short tile words including invalid
phases. They retain the failing `bb` input outside condition (4).
Full native Pell witnesses are not materialized; their existence is
inherited from the complete positive history theorem. No finite test
is used to establish tag universality.
