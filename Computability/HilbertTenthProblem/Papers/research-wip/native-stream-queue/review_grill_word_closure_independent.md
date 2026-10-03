# Independent bounded review of the Grill word-closure compiler

**PASS**, with no source correction requested. The audited source SHA-256 is `144129bb04e271588ed1c95d9c91f5682d30c6b5a540154c6c0b9b0c40331d96`; it is authenticated before execution. This review covers the exact emitted finite-history polynomial, arithmetic ledger, algebraic degree and halting semantics. It does not establish a universal Grill program, a padding-insensitive ordinary-input decoder, or a fixed-arity encoding of an unbounded horizon.

## Independent semantic proof

Fix a nonempty cyclic tuple of natural program numerals n and an externally fixed t>=1. Let H_i=4^(n_i), a_i=2H_i−1. Use positive input x, positive Z0 and positive head witnesses D_i, with d_i=D_i−1. The source computes

```
A0=3x+Z0,
T_i=d_i A_i,       A_(i+1)=A_i+a_i T_i,
E=sum_i T_i,      B=sum_i 2^i d_i.
```

Its final polynomial is

```
F=(A_t−2^t)^2+(Z0+E+3B−2^t)^2+sum_i d_i(d_i−1).
```

Every summand is nonnegative over the integers. Thus F=0 is equivalent to the two endpoint equations and Boolean d_i. This conclusion is not valid over arbitrary real or rational coordinates.

At an integer zero, `A_t=A0 product_i (2H_i)^d_i=2^t`. Hence A0 is a positive power of two, without any unpaid power witness. Since A0=3x+Z0>3x, x is exactly the little-endian content of a uniquely determined binary word w of length log2(A0), including its high zero padding.

Write g_i=`0(10)^n_i`. For a selected head d_i=1, its appendant has length 1+2n_i, scale 2H_i and binary content C_i=2(H_i−1)/3. A_i is A0 times the scales of the previous selected appendants. Consequently the word formed by appending every selected g_i to w has scale A_t and content

```
x+sum_i C_i T_i.
```

The exact telescoping identity `sum_i a_i T_i=A_t−A0`, together with `3C_i=a_i−1`, gives

```
3 value(w G(d)) = A_t−Z0−E.
```

The second endpoint row therefore says `value(w G(d))=B`. Both words have exactly t bits, by the first endpoint row, so the rows are equivalent to the literal word equation `d=w G(d)`.

Process this equation from left to right until the genuine queue first empties. At every earlier step, its front bit is the next d_i and the appropriate appendant is g_i if that bit is one. Cancellation preserves the remaining equality. If the queue has not emptied before step t, its final length is zero, since the entire global equality has length t. Every positive zero thus implies an actual halt at some time τ<=t. Conversely an actual halt at time τ gives a positive closure witness at t=τ.

The fixed-t assertion is deliberately asymmetric. A closure at t may contain a self-consistent suffix after the first empty queue; an actual halt at τ need not extend to a closure at every prescribed larger t for that same initial word. Existential quantification over external t recovers the padded-input halting relation. It does not convert the varying-size polynomial family into one fixed-arity polynomial.

This stop-at-first-empty proof pattern is already present for another substrate in the maintained `binary_tag_four_tile_history.md`, Section 2. The Grill-specific step is the identity `3C_i=a_i−1` and its use to eliminate the full width/content chronology.

## Scope and independent finite evidence

The independent checker enumerates every Boolean head word for six programs `(0)`, `(1)`, `(0,1,1)`, `(1,0)`, `(2,0,1)`, `(0,0,2,1)` and horizons 1 through 10. For each head word, the first endpoint uniquely determines A0. The second then uniquely determines Z0 and x. This gives a complete finite census of positive zeros for those fixed program/horizon pairs, not merely a search in a coordinate box.

Among 12,276 head words, 247 produce positive zeros. Independent literal queue replay gives 227 first halts exactly at t and 20 earlier first halts. In particular, program `(0,1,1)`, x=1, Z0=1, t=6 and heads `100010` satisfies the closure, although the actual initial word `10` halts after three steps. Its putative affine-history width at index 4 is 1/2, so this witness cannot restore a positive-integer width history through all six steps.

No provided creator interpreter is imported. No finite test is treated as a proof of universal computation. The previously identified inconsistency in the creator's Encoding E remains separate from the sound finite word-closure theorem above.

## Exact all-value identity, costs and degree

The direct source computes S0=1 and C0=0, then `S_(i+1)=S_i(1+a_i d_i)` and `C_(i+1)=C_i+d_i S_i`. Its endpoint rows are `P0 S_t−2^t` and `Z0+P0 C_t+3B−2^t`. For arbitrary values of every coordinate, induction gives `A_i=P0 S_i` and `sum_(j<i)T_j=P0 C_i`. This proves identical endpoint residuals and the same entire output polynomial for the direct and shared circuits, without Boolean, sign or zero assumptions.

Let z(t) count phases with n_i=0. The literal default shared source costs `(4t+3−z(t))` multiplications and `(6t+4)` additions/subtractions, totaling `10t+7−z(t)`. The direct source costs `(5t+3−z(t))` multiplications and the same additions, totaling `11t+7−z(t)`. Both have t+1 positive witnesses, t+2 residuals and one positive ordinary input x. Multiplication by a fixed numeral other than 0 or 1 is charged. Constant-only operations and neutral products are folded; every emitted operation is live. These are counts for the actual complete schedules, not lower bounds or counts for an unbounded universal equation.

The exact degree is 2t+2. The highest homogeneous part of A_t is `(3x+Z0) product_i(a_i D_i)`, of degree t+1, and every fixed a_i=2·4^(n_i)−1 is nonzero. Squaring the first endpoint gives a nonzero leading square. It cannot cancel with the other leading square over the reals. The unsquared Boolean factors have only degree two. The all-squared reference has the same exact degree, including t=1. Changing to the unsquared default saves t multiplications and obeys the complete identity `F_squared−F_default=sum_i(B_i^2−B_i)`, where `B_i=d_i(d_i−1)`.

The independent sparse-polynomial executor expands all 144 literal source forms for six programs, t=1,...,6, both direct/shared modes and both Boolean finalizers. It checks 792 individual residual identities, all 144 complete outputs and exact degrees, the charged gate types, source closure, free-coordinate consumption and backwards gate liveness. Its 72 direct/shared comparisons are exact polynomial equalities, not numerical agreement. A further 432 signed public evaluations agree with the independently expanded polynomials.

## Domain and API boundaries

At program `(0,1,1)`, t=3, x=Z0=1 and heads `(1,δ,0)`, direct substitution into the entire default polynomial gives exactly `3333δ^2−δ`. Thus δ=1/3333 is a positive rational false zero with positive D witnesses. The public positive-integer evaluator correctly rejects it. The all-integer nonnegative-factor proof is necessary; there is no claimed real-zero equivalence.

The audited `build`, `checked`, `evaluate` and `decode_zero` interfaces require exact typed program/options/assignments and canonical full packet content. The independent checker confirms 81 malformed-call rejections, including Boolean or floating coordinates, surplus/missing coordinates, all replaced packet fields, and type-only constant substitutions. Two mutation tests confirm fresh direct/shared packets do not share mutable state. Low-level algebra utilities are not claimed to validate arbitrary supplied packets; the public guarded evaluation path is the reviewed interface.

The independent finite census additionally checks both complete emitted modes and their public decoder for all 247 positive closures, giving 494 source-zero/decoder checks. The two explicit boundary fixtures are evaluated algebraically: the post-halt extension demonstrates loss of a causal positive-history bijection, and the rational false zero demonstrates the integer-domain restriction.

## Reproduction and coverage

Run `python review_grill_word_closure_independent.py --expect review_grill_word_closure_independent.json`; `--source PATH` selects the pinned source in another directory. The checker uses only the standard library and authenticates the exact source bytes before executing them in a separate module namespace. It does not import the author's polynomial oracle, fetch external code, or modify repository files. Receipt comparison is recursive and type-sensitive after canonical JSON normalization.

The [checker](review_grill_word_closure_independent.py) and [receipt](review_grill_word_closure_independent.json) contain the complete finite census and scope counterexamples. This is a source/proof/API review of this bounded compiler, not a review or validation of the full informal Genera-to-Grill universality compiler. No new fixed-arity universal arithmetic bound follows from the varying-horizon ledger.

The full companion proof note was also read, including its post-halt family, all-value source transformation, complete ledger table and explicit fixed-t asymmetry. Its reviewed pre-provenance SHA-256 is `6da06658577171b8fa7282abc751e1e5e8032c780246894bb0069c8ebadc5c51`. The author source was not changed. Independent writer and fresh exact saved-receipt replay both passed.

Root read the final source and both proof notes, then replayed the author and
independent suites from the maintained directory. Both fresh receipts match
their frozen counterparts byte for byte.
