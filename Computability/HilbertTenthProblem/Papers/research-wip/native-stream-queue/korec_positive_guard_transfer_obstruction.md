# Why deleting the packed zero guard does not inherit the local selector saving

The scalar complement reuse and vector positive-selector theorem do not
currently yield a cheaper complete packed history source. A specific tempting
one-addition deletion in the actual 376-operation U21 source is **unsound**:
its program-2 slice acquires a positive zero at ordinary input1, although
the actual machine diverges there. More strongly, the same symbolic forged
trace works for every positive ordinary input. This refutes preservation
of this compiler's exact program/halting interface; it is not a theorem
that the altered polynomial could have no universal slices whatsoever.

The result below supplies an explicit 88-step trace, a fresh proof of
genuine divergence, all outer witnesses, exact paid source accounting and
a positive native-extension argument. No saved source array or frozen
helper was executed. It is a bounded obstruction, not an impossibility
claim for every future packing of the new vector theorem.

## 1. Which existing history interface is being tested

`residue_affine_packed_history.md` compiles a fixed expanded residue table
by selector submasks and selected quotient products. Its literal source
does not contain the scalar six-witness graph's per-step U,V,PT complement
equation. Thus replacing its scalar guard residual by the sum with that
complement is not a syntactic edit available in this packed source. An
independently aligned packed encoding of those witnesses could still use
the exact linear residual identity; it would have to pay its own lookup,
products, bounds and chronology. The 134-operation Collatz orbit source
does not thereby gain a universal-input or lower arithmetic-count claim.

The direct-register route already avoids a separate Boolean polynomial
per step. Its actual current default is the 376-operation source in
`korec_packed_repunit376.json`, with one fixed positive program parameter E,
ordinary positive input x, 50 positive witnesses and degree bound21549.
The zero/range masks were previously merged by zero_range397. With

    h=E+x+eta, D=2h, B=D^8,
    E_i=edgehat_i-1, J=sum E_i, P=(B-1)J+1,
    V=1+D+...+D^7,
    Zword=sum_(zero edges i) D^register(i)*E_i,

its combined mask is `Rstar=(h-1)(VJ-Zword)`. The selector lanes and
`W AND Rstar=W` encode one edge per time, counter bounds, and the
selected zero condition. Positive decrement and positive pure-test
branches already use post-decrement counters, so their positive tests
are supplied by the current counter being the stored digit plus one.

## 2. A fully charged but rejected one-addition candidate

The exact one-program `units` array contains

    counter_digit_mask_92 = counter_repunit_91 * partition_66
    counter_M_325 = counter_digit_mask_92 - Z_sum_146
    range_mask_93 = counter_half_minus_one_84 * counter_M_325.

Their values are VJ, VJ-Zword and Rstar. Delete only the middle row and
redirect the last operand to `counter_digit_mask_92`. This replaces Rstar
everywhere by `R0=(h-1)VJ`, including both the global range unit and the
native mask. The deleted value has only this one consumer. Z_sum_146
remains live in current_base_159, so its computation is not a private
zero-test expense that can additionally be subtracted.

Structural inspection of the actual complete array gives the rejected
candidate exactly **375=143M+232A**, with the same two external parameters,
50 positive witnesses, all retained rows/ports live and the same final
product-minus-one shape. This is one fewer addition than376=143M+233A.
It is not an accepted compiler improvement. No numerical or symbolic
interpreter was applied to either the saved or mutated source array.
The changed source is used only as an authenticated dependency graph;
Sections4–5 bind its values by fresh mathematical outer formulas and the
inherited native theorem.

**Remark 1 (retained failed proposal).** The assertion that positivity
makes the selected zero-clearing subtraction redundant is false for this
source. The explicit program-2 counterexample below is retained with this
rejected375-operation count. The previously accepted local vector proof
has a separate product guard; it never asserted that this guard can also
be removed.

## 3. Genuine divergence and the single false zero branch

Use the exact 21-state, eight-register table of `korec_packed_counter_units.md`.
States are0,...,20 and halt21. Program E=2 starts at

    (R0,...,R7)=(0,2,X,0,0,0,0,0), X>=1.

The following 59 successive instruction states, each taking its genuine
branch, return to state0 with vector `(1,2,X,0,0,0,1,0)`:

    0,1,0,1,0,2,3,4,5,6,7,4,3,2,3,4,5,6,7,4,
    3,2,3,4,5,6,8,0,1,0,1,0,2,3,2,3,4,5,6,7,
    4,5,6,7,4,3,2,3,2,3,4,5,6,8,9,10,11,14,19.

From state0 with vector `(A,2,X,0,0,0,1,0)`, A>=1, the 30 genuine
instruction states

    0,1,0,1,0,2,3,4,5,6,7,4,5,6,7,
    4,3,2,3,2,3,4,5,6,8,9,10,11,14,19

return to state0 with vector `(A+1,2,X,0,0,0,1,0)`. These are exact
affine identities and branch conditions for all A,X>=1. No halt occurs.
Induction therefore proves genuine nontermination for every X>=1.
This reproduces the prior divergence argument rather than trusting a
receipt's status or extrapolating a finite nonhalting simulation.

Now follow the 59-step prefix and the first26 steps of that loop, at A=1.
At time85, immediately before state10, the vector is

    (1,2,X,0,0,1,1,0).

State10 is `D 5 11 12`; its tested register is1, so the genuine branch
is the positive one. Falsely take its zero branch to12, leaving every
counter unchanged. State12 is `D 2 17 18`, and the ordinary input X>0
allows its genuine positive decrement to17. State17 is `D 4 0 21`;
R4=0 makes its genuine zero branch halt. The final vector is

    (1,2,X-1,0,0,1,1,0).

This is an88-row path with exactly one false guard, at time85. All selected
edges exist in the actual U21 table; every control adjacency and every
numerical counter update, including the false zero branch's unchanged
inactive and active counters, is exactly the corresponding edge update.
The one-step ZERO/DEC theorem rejects it precisely by its zero guard,
not merely by positivity of the unchanged counter.

## 4. Positive outer witnesses and exact packed identities

First take X=x=1, E=2 and h=16, so eta=13, D=32 and B=D^8=2^40.
Let T=88, P=B^T and J=(P-1)/(B-1). Pack the actual selected edges into
E_i with digits0 or1. For each row use its before vector as the stored
post-decrement vector, subtracting one from its addressed register on
positive D or positive pure-test T edges. The false zero row requires
no subtraction. All stored digits lie in[0,h-3]. Let W be their chronological
word and Y the final counter vector packed in base D. Let I,L be the
increment and positive-decrement words, with a positive pure-test edge
contributing to both, as in the current source.

The native control codes are `code(s)=lambda_s D^register(s)`, with the
accepted labels

    (1,2,2,1,1,2,1,2,3,1,3,4,1,5,1,2,2,3,1,2,2),

and `code(halt)=0`, `code(start)=D`. Direct coefficient comparison of
the88 rows gives

    sum E_i=J,          E_i AND J=E_i,
    B(W+I)+2D+D^2 = W+L+P*Y,
    B*following+D = current.                            (1)

There is no borrow or carry in these identities: each stored counter
digit is nonnegative, the selected action changes one digit by at most1,
and all resulting counter and control digits are below their radices.
The unaltered control/source sum is used; the selected zero word is
still paid there.

The relaxed mask `R0=(h-1)VJ` permits every stored digit, so
`W AND R0=W`. Choose the positive global slack

    gamma=R0-W-2.

It is positive because each of the eight range digits is h-1 and the
stored digits are at most h-3; in particular their digitwise differences
are at least2 with no borrow. The range unit is exactly
`R0-(W+1+gamma)=1`. Both transport units are1 by(1).

All genuine zero branches had a zero tested digit. Only the forged row
has a nonzero digit under a zero-cleared mask. Thus the exact obstruction is

    W-(W AND Rstar) = D^5 B^85 != 0.                    (2)

The helper checks this equality, not only failure of the old AND.
Every selector hat is E_i+1>0, W_hat=W+1>0 and Y_hat=Y+1>0; unused
selectors are allowed to have hat1. These and eta,gamma account for38
outer witnesses. No extra coordinate encodes X or supplies a duration.

The same88 symbolic rows work for arbitrary positive X: choose any dyadic
h greater than X+4 and the fixed counter values, and put eta=h-2-X>0.
The argument and all positive margins persist. The numeric receipt fixes
only x=1; this quantified extension follows from the displayed affine trace.

## 5. Completing the false zero with positive native witnesses

Let

    Cpack=sum_(i=0..33) E_i P^i,
    Cmask=J*(1+P+...+P^33),
    H=Cpack+P^34 W, M=Cmask+P^34 R0, Q=B P^35.

Here P is dyadic and every lane coefficient is below P. All selector
lanes and the relaxed range lane hold, so `H AND M=H`, with
`0<=H<M<Q`. The prescribed padded native scale is q=16Q, and its
four actual computed fields are

    F0=16(Q-M)-15, F1=4, F2=16(M-H)+2, F3=16H+8.

They are strictly positive, sum identically to q-1 and have the required
residues1,4,2,8 modulo16. Thus the complete prescribed-AND extension used
by zero_range397 applies. This argument uses the native theorem at its
actual positive interface; it does not invoke the complete halting theorem
whose zero-guard hypothesis is deliberately false.

The same canonical normalized/coupled native construction makes all six
native factors +1. Its canonical native X is2^(2r+1), where the packed
native index r=(q-1)S is greater than q. The supplied bound coordinate
beta_native=X/q-S is a positive integer: q is dyadic, its binary exponent
is below2r+1, and X/q>r>=S. Hence the literal bound-only source
`X=q*(S+beta_native)` is respected. All other private native coordinates
come from the inherited full positive extension, unchanged in meaning.

The three outer factors are already +1. Therefore the actual modified
nine-factor product-minus-one polynomial has a full positive zero at
E=2,x=1. Exactly twelve private native witnesses complete the38 explicit
outer witnesses; no huge Pell integers need to be numerically materialized.
The original E=2 slice is empty by Section3. This is a projected-language
counterexample for the authentic compiler, not a free-port scalar example.

## 6. A second, smaller obstruction to a direct word-product transfer

The local vector theorem uses `(beta_t-2)G_t=0` at each time. Even if the
correct words of both factors were already available, replacing all those
tests by their ordinary integer word product is invalid. A legal zero
test of a zero counter followed by an increment of that counter has

    t_digits=(-1,0), G_digits=(0,2L).

Both componentwise products vanish. In time radix b, however,
`t_word=-1`, `G_word=2Lb`, and their product is `-2Lb`, nonzero.
An ordinary product convolves time positions. Other registers can contain
the ordinary positive input unchanged. This counterexample concerns that
specific naive substitution, not all synchronized product encodings.

The positive selector argument removes a redundant Boolean constraint
after the local product guard is paid. The current packed source instead
pays edge typing and a synchronized zero/range mask, so neither deleting
that mask nor replacing it by an ordinary word product inherits the proof.
No cheaper complete counter-history source was established in this bounded
investigation. A different paid synchronized product/control encoding is
left open rather than assigned the scalar or finite-step cost for free.

## 7. Evidence, provenance and execution limits

The fresh helper reads the pinned current array as data, checks the exact
removed row and its sole consumer, and verifies closure, liveness and paid
counts of the rejected replacement. It never evaluates either array.
Its own newly handwritten symbolic interpreter verifies all59 prefix and30
cycle transitions with affine coordinates `(constant,A,X)` for all A,X>=1,
including every branch and nonnegative counter condition. It records the
full88-row forged trace and the unique false guard. Its separately written
packing formulas check(1), (2), all relaxed lanes, positivity and checksum.
At x=1, P has3521 bits and Q has123241 bits; native Pell witnesses were
not computed. No finite cutoff is used to infer genuine nontermination.

Fresh normal and optimized runs from `/` passed with byte-identical
receipts before freeze. No supplied, frozen, committed, copied predecessor
helper, builder or source array was executed/imported. No repository or
Git mutation occurred. Earlier adversarial-zero tests remain earlier work;
the present contribution is this actual program-2 projected-language
counterexample bound to the exact one-row375 proposal.

| Inert dependency | SHA-256 |
|---|---|
| `korec_packed_repunit376.json` | `3500e3426afba2ac4f83093240f4bc2ccf89cac84df1cb592853e9485a3f3b1f` |
| `korec_packed_repunit376.md` | `cae83d590e277a43e45f9f8b5be514ea701aa59c98bba45586ab874004fb31a2` |
| `korec_packed_zero_range397.md` | `ae542cedc61c0231d797b2e5a2bb9ce0e9a639ece389b81618ba871fac5c4ed4` |
| `korec_packed_positive_program410.md` | `4e8c02aff21d80ad5d7cb6543743214ce0c33556bc0bb5f1bf30d20068eee13e` |
| `korec_packed_counter_units.md` | `02cd6d353cf66db83b88b616655f59c072bf64cea8e07dc5ad37b8fd3c553437` |
| `korec_packed_counter_compiler.md` | `834d5622ebe1acd46d201e5b4a561e285feb47ef3870bd9274b6dd99fca5477e` |
| `residue_affine_packed_history.md` | `0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882` |

These proof notes were read inertly for the stated packing, domain and
extension interfaces; no new external primary-machine review is claimed.
The fresh helper SHA-256 is
`68c8895a1a2c0e72f41825ae7c41ff418dca16bd29d9e1dba6185a924a92ef86`.
The receipt SHA-256 is
`f6c771b9a0b2e582375178df47c7618da26e8d15a720afd196793a229d7804ac`.
