# Configuration brackets remove the fresh history separator

The explicit universal construction now costs **1046=423M+623A** polynomial
operations, with **162 positive witnesses**, three positive program
parameters and exact degree **199806**. The certificate has966=396M+570A
operations and27 comparisons. Supplying the initial history value gives
**1049 operations**,163 witnesses,28 comparisons and degree **7276**.
The universal75/88 frontier remains smaller.

This is a successor to the [prefix-coded universal table](neary_woods_prefix_universal.md)
and the [state-free ordinary-machine compiler](gpcp_state_free_copies.md).
It removes the fresh `#` copy tile and both occurrences of `#` in the
endpoint framing. Configuration brackets already force the row boundaries.
The [source](gpcp_bracket_anchored_history.py) and
[receipt](gpcp_bracket_anchored_history.json) include the complete new source.

## 1. Word theorem with no extra separator

Use a fixed Turing machine's bounded-tape transition and accepting-cleanup
rules. The tape alphabet Gamma and state alphabet Q are disjoint and do
not contain the bracket symbols. A configuration is a word

    [ tape-left state tape-right ]

with exactly one opening bracket, one closing bracket and one state.
Every genuine transition or cleanup preserves these properties. All left
and right rule sides are nonempty; each contains exactly one state. If a
rule side contains `[`, it is its first symbol; if it contains `]`, it is
its last symbol. In particular no rule side crosses a boundary `][`.

Keep all rewrite tiles `(l,r)` and copy tiles `(a,a)` for tape symbols and
the two brackets. There are no state-copy tiles and no fresh separator.
Let sigma and tau be the two concatenation morphisms of this tile table.
For distinct valid initial and target configurations u and v,

    u derives v  iff  sigma(w) v = u tau(w)

for some nonempty tile word w. The needed theorem concerns these bracketed
configurations; it is not the unrestricted rewriting-to-GPCP theorem with
its fresh delimiter silently deleted.

For completeness, encode each actual rewrite `u_i = a l b -> a r b = u_(i+1)`
by copies of a, its one rewrite tile, and copies of b. The contexts contain
no state, so all these copies exist. Concatenating these rows gives

    sigma(w) = u_0 u_1 ... u_(m-1),
    tau(w)   = u_1 u_2 ... u_m.

Appending `u_m` to the first word and prepending `u_0` to the second gives
the required equality. No separator tile is inserted between rows.

For soundness, suppose the displayed equality holds. If w is empty it
forces u=v. Otherwise sigma(w) is nonempty since all tile upper words are
nonempty. If `|sigma(w)|<|u|`, the initial `[` of the appended v would occur
strictly inside u after its sole opening bracket, which is impossible.
Thus u is a prefix of sigma(w). Its final `]` lies at a tile boundary:
every occurrence of `]` in an upper tile word is its final symbol.

Cut off the tile prefix whose upper concatenation is exactly u. This
prefix contains exactly one rewrite tile, since u contains exactly one
state, rewrite tiles each consume one state, and no state is copied. All
its remaining tiles are literal copies. Its lower concatenation is
therefore the valid next configuration u1 from one actual rewrite of u.
Writing the remaining tile word as w1, cancel u in the original equality:

    sigma(w1) v = u1 tau(w1).

Repeat. Each cut removes at least one tile, so this process terminates.
The last equality with an empty remaining word says the final configuration
equals v. This gives an actual derivation in its original chronological
order. It also proves that a solution cannot hide a partial last row in
the appended target configuration.

The compiler's initial state differs from the accepting state. Its input
u is therefore different from `v=[accept]`, so no reflexive or empty-word
case is needed by the positive-duration affine history.

## 2. Complete arithmetic composition

For a fixed ordinary machine, retain the old alphabet codes and width.
The unused `#` code may remain in that dictionary; it appears in no tile or
endpoint. Rebuild the input suffix as `]`, the terminal as `[accept]`, and
the tile table with tape/bracket copies plus the original rules. The paid
ordinary input recoder, prefix and optional program loaders are unchanged.
The resulting word equation is compiled through the full selected affine
history, with its own positive witnesses and fresh packing geometry.

For U15,2 use the same fixed prefix code and paired input convention as the
parent. Removing the unused separator leaves **96 physical tiles: four
copies and92 rules**. Prefix-code injectivity still gives equality of
physical words from equality of binary encoded words. A `#` bit pattern
inside an encoded word is irrelevant: no parsing argument treats a bit
pattern as a fresh separator.

The ordinary input block width remains64, and the paid block repunit and
bit morphism still compute D from x. Its three positive program parameters
now encode

    p = sentinel(prefix),
    a = 2^(bit length of suffix),
    b = value(suffix),

where the suffix is `A_right A_left ]`, without `#`. Its last bracket has
a nonzero code, so b>0. The source computes the same strictly positive
framing expression `Vi=a(pQ+D)+b` in four gates. The terminal expression
now appends only `[halt]` to the upper history. Both terminal gates remain
paid with their new literal constants.

For each r.e. positive-integer language, the parent simulation supplies
the same finite U15,2 program and the same padded physical input. Changing
the suffix parameters and terminal word as above, the new word theorem
gives acceptance in both directions. The complete affine history then
supplies all selector, range, duration and native typing. The three-core
unit projection retains all strong comparisons and its safe checksum
arrangement. Consequently one fixed new polynomial F satisfies

    x in S iff exists y_1,...,y_162 > 0:
               F(x,p_S,a_S,b_S,y_1,...,y_162)=0.

The three program values are fixed parameters, not existential witnesses.
The theorem is for valid program slices. It asserts neither that arbitrary
positive parameter triples encode configurations nor that new and old
numeric polynomials agree on identically named witness tuples.

## 3. Counts and exact degrees

There are still six exceptional slope products. The scale exponent falls
from107 to **N=96+6+4=106**. With the parent's tuned codeword assignment,
the paid planner selects raw-history cost **H=812=310M+502A**, down from823.
The complete certificate cost is `H+148+ell(64)=966`, since `ell(64)=6`.
Its27 comparisons yield the1046-operation polynomial. The reduction is
eleven operations; it includes the actual recomputed power-chain and
transport schedule, rather than assuming a fixed saving per removed tile.

| Code assignment / initial value | Certificate | Polynomial | M+A | Witnesses | Degree |
|---|---:|---:|---|---:|---:|
|Tuned / computed|966|1046|423M+623A|162|199806|
|Tuned / supplied|966|1049|424M+625A|163|7276|
|Original balanced / computed|974|1054|431M+623A|162|199806|
|Original balanced / supplied|974|1057|432M+625A|163|7276|

All four free variables x,p,a,b and all positive witnesses have degree one.
The parent exact-degree audit applies to the rebuilt source, with
`k=64`, `v=k+2=66`, and `nu=k+3=67` when Vi is computed or `nu=2` when
supplied. Put `d_H=N nu`. The degree is

    14 + 19v + 20d_H - 6nu + 84 + 8 max(d_H,v).

The audit verifies every main-norm cancellation prerequisite and evaluates
a nonzero highest homogeneous coefficient; it does not reduce degree using
relations valid only at zeros.

For the same ordinary odd-integer example, the table drops from30 to29
tiles. The default polynomial drops from587 to **579=249M+330A**, with93
positive witnesses and degree5502. The receipt also retains raw and
supplied-endpoint variants for four ordinary machines. These example
machines are decidable and are separate from the explicit universal table.

## 4. Verification scope

The replay checks the emitted complete residual/SOS or unit-product
identities on signed assignments, and independently constructs finite
derivations for odd, even, all-input and return-left machines with padding.
The separator-free word encoder and the converse decoder reconstruct the
same ordered rewrite steps. Terminal equality accepts exactly the expected
inputs in those finite fixtures; dense append agrees with their positive
outer history endpoints.

Additional checks audit the prefix-coded universal table's complete
arithmetic counts and degrees, padded program frames without `#`, and
arbitrary selected word append/injection identities. These tests support
the bracket-cut and positive-extension proofs. Full native Pell witnesses
are supplied by the component converses, not materialized by finite tests.

Run the default receipt comparison with:

```sh
/tmp/diophantine-research-venv/bin/python gpcp_bracket_anchored_history.py
```

Author generation and fresh replay pass. Independent full proof/source
review and fresh default replay also pass without findings. The reviewer
additionally checked335923 candidate tile words in a small anchored system,
reconstructed its sole bounded solution, and checked72 signed complete
source identities with free/fixed loaders and both endpoint conventions.
An earlier independent proof check verified the bracket-cut induction.
