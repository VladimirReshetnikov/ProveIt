# Complete compilation of sparse, oriented machine histories

The explicit U15,2 universal construction has a **810-operation polynomial,
349M+461A**, with **125 positive witnesses**, three positive program
parameters, and exact degree **130394**. Its certificate has
**730=322M+408A** operations and **27 comparisons**. Supplying the initial
history value instead gives **813 operations**, 126 witnesses, 28 comparisons
and degree **5204**. These are complete ordinary-input universal
polynomials; the separate 75/87 universal arithmetic frontier remains smaller.

This packet composes the proved [sparse machine rules](sparse_tm_rewriting.md)
with the [bracket-anchored word theorem](gpcp_bracket_anchored_history.md),
the paid [prefix-code input bridge](neary_woods_prefix_universal.md), and
the complete [slope-class compiler](gpcp_slope_class_compiler.md).
The [source](gpcp_sparse_tm_compiler.py) rebuilds every changed numeric table
before applying the arithmetic planner. The [receipt](gpcp_sparse_tm_compiler.json)
contains the exact default source and the other audited ledgers.
No earlier table, code assignment or receipt is changed.

## 1. Symbolic and ordinary-input contract

Fix a deterministic machine with a finite tape alphabet containing the
blank, a distinct initial and accepting state, and no outgoing accepting
instructions. The ordinary wrapper additionally requires tape symbols
`0` and `1`. A fixed orientation places each state either before or after
its scanned tape cell. The initial state must be **before**. Thus the paid
input word `[start bits]` is literally unchanged, including every allowed
leading-zero padding and optional fixed or positive-parameter program
loader. An after-oriented initial state is rejected by this API; there is
no uncharged conversion moving it across a variable input bit.

To obtain an ordinary-input language S from the generic wrapper, require
the machine to accept **every permitted leading-zero padded spelling** of
x exactly when x belongs to S, as in the parent compiler contract. For a
machine without this invariance, the exact arithmetic projection instead
recognizes inputs having some accepted permitted padded spelling. The
fixed-initial-configuration rewrite equivalence itself needs no padding
invariance.

The sparse helper emits one local rule for a right move entering a
before-oriented state, and one for a left move entering an after-oriented
state. At a nonaccepting boundary, a shared state-specific rule inserts
the missing scanned blank. The other movement cases retain their
neighbor-specific transition rules. A pending nonaccepting state has
exactly its forced repair available; it cannot take an ordinary transition
until the scanned cell is restored. Pending acceptance needs no repair,
because accepting cleanup erases the explicit tape. These facts give the
helper's complete acceptance equivalence, including undefined blank
transitions, both tape boundaries and infinite nonaccepting runs.

Every emitted rule has nonempty sides, exactly one state on each side,
and brackets only at the appropriate end. Keep copy tiles for tape
symbols and the two brackets, and no state or `#` copies. The
bracket-anchored theorem therefore applies to all transition, repair and
cleanup rows. In particular, for the valid initial word u and
`v=[accept]`,

    machine accepts u  iff  sigma(w) v = u tau(w)

for some nonempty tile word w. Its row-cut converse recovers actual sparse
rewrite rows in chronological order; compressing their forced repairs
recovers the original machine computation. The unique initial state
differs from accept, so u differs from v and the empty tile word cannot
be a solution. A declared isolated initial state simply rejects.

The generic API is

```python
build_for_tm(tape, transitions, start, accept,
             orientations=None, rule_order='grouped',
             width=None, unit_product=True, regroup=True,
             factor=True, history_choice='auto', **loader_options)
```

`orientations=None` means all-before. `incoming_orientations` supplies a
deterministic per-target rule-count choice subject to start and accept
remaining before-oriented. It is an optional fixed-table choice, not an
existential runtime field or a claim of globally minimum arithmetic cost.
The universal table below uses its own explicitly specified orientations.

The default rule order keeps the helper's instruction-rule order, sorts
the repair rows lexicographically, and places left-context accepting
cleanup before right-context cleanup. The source proves equality of the
two rule sets and equality of their cardinalities. This is a fixed
permutation of tile names: a word in either table has its same sequence
of physical rewrites in the other. It changes the paid arithmetic planner's
opportunities without changing machine chronology. `rule_order='helper'`
retains the original helper order.

## 2. Fresh complete arithmetic histories

For an ordinary fixed machine the source retains the parent alphabet,
literal symbol codes, width and optional loader. It replaces the rules,
forms the new tape/bracket copy table, and encodes that exact new table.
It then calls the complete raw builder with prefix `[start`, suffix `]`
and terminal `[accept]`. Only afterward does the guarded slope-class
planner operate on these newly compiled maps. Its same-map check is
retained. An inherited numeric table for the old rules is explicitly
discarded from the public symbolic metadata.

For each tile `(upper,lower)`, its two append maps are

    U -> 2^len(upper_bits) U + value(upper_bits),
    V -> 2^len(lower_bits) V + value(lower_bits).

Both words are nonempty, so their slopes are positive powers of two and
their offsets are nonnegative. These are exactly the hypotheses of the
complete affine history. That construction pays for the common arbitrary
positive duration, binary geometry, one-hot selector stream, canonical
history digits, selected slope-class products, and both affine transports.
Its raw or unit-product source is used without deleting a guard.

Soundness first recovers the paid input recoding and a real selected tile
word. The terminal equality, injective code, bracket row decoder and
sparse-run theorem then give acceptance of the same ordinary input.
Completeness runs the original machine, emits the corresponding sparse
rows and copied contexts, and constructs a new positive arithmetic
history for that word. Its native witnesses and packing lengths are
fresh. All the parent positive extensions, root-gap maps and retained
strong comparisons apply to the newly emitted source. No bijection or
off-zero polynomial identity between the old and new *tables* is asserted.

This proves the generic compiler theorem for valid normalized starts and
the chosen ordinary-input convention. It does not identify arbitrary
malformed boundary tuples with machine configurations. Raw SOS,
slope-class/per-tile choices, supplied/computed initial history values,
and fixed/positive-parameter loader options remain available.

## 3. The explicit 57-tile universal table

Use the same U15,2 Table16 transitions and accepting adapter as the
[explicit universal packet](neary_woods_explicit_universal_tm.md): two tape
symbols, 14 right moves, 15 left moves and one stationary accepting adapter.
Choose before orientation for

    u1, u12, u13, u14, u15, halt,

and after orientation for `u2` through `u11`. This keeps the actual initial
state u1 before its scanned cell. There are 27 local moving instructions,
two contextual moving instructions, five shared right repairs, ten shared
left repairs, one stationary rule and four cleanup rules. The count is

    27 + 3*2 + 5 + 10 + 1 + 4 = 53 rewrite rules,
    53 + 4 tape/bracket copies = 57 tiles.

The all-before comparison has 71 rewrite rules and four copies, hence 75
tiles. The historical bracket table had 96 tiles. Every count comes from
the actual emitted helper rules, not a guessed saving per removed tile.

The default `sparse_tuned` prefix code starts with the parent's ordered
balanced code and swaps the codewords for `(u10,u12)`, `(u4,u6)` and
`(u7,u9)`. It preserves the codeword multiset: tape symbols still have
length two, states length five and brackets/accept length seven. The
source verifies prefix-freeness and these exact fixed swaps. The code is
fixed data chosen before compilation; the search that found it is not a
runtime arithmetic operation or an optimality claim. The balanced and
older prefix-tuned assignments remain explicit alternatives.

The physical input bit blocks are unchanged. Each has 32 tape symbols and
therefore 64 encoded bits. The paid recoder and bit-block morphism continue
to compute that same padded ordinary-input word. Only fixed state-code
numerals in its prefix and other fixed framing numerals are recomputed
under the selected dictionary. For each represented language, the three
positive fixed program parameters are

    p = sentinel(physical prefix),
    a = 2^(encoded suffix length),
    b = value(physical suffix),

where the suffix ends with `]` and contains no `#`. It has b>0. The paid
framing expression is `Vi=a(pQ+D)+b`; terminal appending uses the actual
new `[halt]` code. Prefix injectivity recovers the same physical words.
Changing orientations affects intermediate encodings, while u1-before
preserves the literal universal initial configuration.

Consequently there is one fixed polynomial F such that, for every r.e.
positive-integer language S, the inherited effective universal simulation
supplies fixed positive parameters p_S,a_S,b_S with

    x in S iff exists y_1,...,y_125 > 0:
               F(x,p_S,a_S,b_S,y_1,...,y_125)=0.

These are three parameters, not existential program witnesses. The claim
is for the valid program slices supplied by the inherited simulation;
arbitrary positive triples need not encode a valid machine configuration.
Leading-zero input padding has the same harmless meaning as in that
simulation. No new universality theorem is inferred from finite U15 traces.

## 4. Literal counts and degrees

The default actual slope-class planner chooses baselines 128/128 and eight
exceptional selected products. With 57 tiles its scale exponent is
`N=57+8+4=69`. Its complete raw history costs **H=576=236M+340A**.
The U15 bridge and unit projection give

    certificate = H + 148 + ell(64) = H + 154 = 730,
    polynomial  = H + 228 + ell(64) = H + 234 = 810,

where `ell(64)=6`. The 27-comparison finalizer adds 27M+53A to the
certificate, giving the stated 349M+461A. Supplying Vi retains one extra
positive witness and comparison, adding one multiplication and two
additions to the final polynomial. The supplied certificate is unchanged.

| Oriented code / initial value | Certificate | Polynomial | M+A | Witnesses | Degree |
|---|---:|---:|---|---:|---:|
|Sparse tuned / computed|730|810|349M+461A|125|130394|
|Sparse tuned / supplied|730|813|350M+463A|126|5204|
|Balanced / computed|735|815|354M+461A|125|130394|
|Balanced / supplied|735|818|355M+463A|126|5204|
|Older prefix tuned / computed|736|816|355M+461A|125|130394|
|Older prefix tuned / supplied|736|819|356M+463A|126|5204|

The receipt additionally records the old prefix-tuned code, all-before
orientation comparisons, and generic ordinary-machine examples. All
literal source gates, fixed-coefficient products and scalar comparisons
are included. Fewer symbolic rules alone would not justify these costs;
the actual new histories and paid linear-form plans establish them.

For the all-before 75-tile table, the older prefix-tuned assignment gives
H=735 and **969=401M+568A** polynomial operations, 143 witnesses and degree
164162; supplying Vi gives 972 operations, 144 witnesses and degree 6212.
These alternatives keep the same ordinary-input theorem and make the
effect of changing the state orientations separately reviewable.

The ordinary odd-integer example drops from the bracket parent's 579
operations to **491=222M+269A**, with 19 tiles, 81 witnesses and degree 3822.
Its raw history is H=269 and its complete certificate 414=196M+218A with 26
comparisons. The return-left example demonstrates an orientation saving
within the same semantic machine: all-before 578 operations become 494
with an after-oriented returning state. These are finite decidable test
machines, not the explicit universal language construction.

All four universal parameters x,p,a,b and every positive witness have
degree one. The parent exact-degree checker is applied to the actual new
source. Set `k=64`, `v=k+2=66`, `nu=k+3=67` for computed Vi and `nu=2` for
supplied Vi, and `d_H=N nu`. The exact polynomial degree is

    14 + 19v + 20d_H - 6nu + 84 + 8 max(d_H,v).

The audit checks the literal prerequisites for all three main-norm
cancellations, propagates the remaining homogeneous degrees, and gives
a nonzero evaluation of the highest form. It uses no equality valid only
on the zero set. For N=69 this gives 130394 or 5204, respectively. No degree
claim follows merely from retaining the codeword lengths; the actual
changed arithmetic source is audited.

## 5. Verification and limitations of finite checks

The default replay records 52 exact ledgers and 456 complete raw
residual/SOS or unit polynomial identities, including 228 signed
assignments. These cover both endpoint conventions, per-tile and
slope-class histories and optional
loaders. Every emitted arithmetic source is acyclic with unique register
names, and its M/A histogram agrees with the recorded literal ledger.

Every emitted rewrite rule is independently wrapped in three valid
bracketed contexts and encoded as a tile row; the converse decoder
reconstructs that exact rule and location, giving 738 local/cleanup row
checks. Additional cleanup rows and odd, even, all-input and return-left
computations check chronological
derivations with zero padding. The independent sparse-helper audit covers
all source/target orientations, forced repairs at both boundaries,
undefined transitions, pending acceptance and long runs; that theorem
supplies the unbounded machine correspondence used here.

The complete-source fixtures separately check strictly positive outer
coordinates on 99 genuine outer runs, the first five recoder comparisons,
the three outer history comparisons, dense append and the terminal equality.
They do not claim
that arbitrary placeholder native coordinates solve the remaining Pell
comparisons. Those positive extensions are supplied by the proved
component converses. Universal checks verify 288 paid parameter frames
and 288 prefix decoding/selected word append cases, without pretending
that these packing-only words are accepting machine runs.

```sh
/tmp/diophantine-research-venv/bin/python gpcp_sparse_tm_compiler.py
```

Author receipt generation and fresh default replay pass. Independent root proof/source review
passes without findings, supplemented by 48 signed complete-source
identities on the default and supplied variants. A second independent
proof/source review also passes, with 2,500 local rows on 96 random oriented
machines, 576 tile-permutation/numeric-append checks, and 72 positive program
frames across the three code assignments. Both reviewers' independent
fresh default replays pass without findings. Historical packets retain their original
sources, scopes and operation counts.
