# Sparse machine rules with shared boundary repair

A fixed deterministic Turing machine need not repeat every right-moving
instruction once for each possible neighboring tape symbol. With the usual
state-before-scanned-cell representation, replace those rules by the one
local rule `qa -> bp`, then share `p] -> p_]` among all right moves entering
the same nonaccepting state. The latter repair is forced at a pending right
edge, and is unnecessary when the new state is accepting.

The [stdlib-only helper](sparse_tm_rewriting.py) and
[receipt](sparse_tm_rewriting.json) also allow a fixed orientation for each
state: before or after its scanned cell. After-oriented target states make
left moves local, with the symmetric shared left-edge repair. The default
is all-before, retaining the original literal input representation and
every original left/stationary rule.

This packet proves accepting-run equivalence and literal symbolic-rule
counts. It does not assign an arithmetic operation count or change any
earlier compiler, table or navigation file.

## 1. Contract and API

The tape alphabet is a nonempty tuple of distinct symbols containing the
blank `_`. It is disjoint from the state symbols and the reserved bracket
and separator symbols. A deterministic transition dictionary maps

    (state, read) -> (target, write, direction),  direction in {L,R,S}.

Read and write symbols belong to the tape alphabet. The designated
accepting state has no outgoing transitions. This is the usual halting
acceptance convention; outgoing instructions at a halting accepting state
can be discarded when specifying the machine. Missing nonaccepting
transitions halt without acceptance.

The reusable API is

```python
rewriting_rules_sparse(tape, transitions, accept, orientations=None)
```

It returns the same tuple of `(left_word, right_word)` pairs as the existing
context-enumerated rule helper. `orientations` is a partial fixed dictionary
from state to `'before'` or `'after'`; omitted states use `'before'`.
Unrecognized state keys and orientation values are rejected. The source
also exposes `right_repair_states`, `left_repair_states`,
`encode_configuration` and `normalize_configuration` for inspection and
proof checks. There are no runtime existential orientation choices.

The rule API learns its state set from transition sources, targets and the
accepting state. An isolated declared initial state needs no rules and
rejects immediately; the run checker handles this case explicitly. A
caller with a larger declared state dictionary should restrict the
orientation map to states occurring in the rule API before calling it.

A semantic normalized tape window consists of a left tape word `l`, a
state q, and a nonempty current/right word `a r`. Its encoding is

    before(q):  [ l q a r ]
    after(q):   [ l a q r ].

There is one opening bracket, one closing bracket and one state. The
current symbol must actually be present at a normalized nonaccepting
start. Pending representations with a missing current symbol are reserved
for the intermediate boundary case described below; they are not silently
allowed as arbitrary initial configurations.

For the ordinary fixed-prefix input compiler, require the initial state's
orientation to be **before**. Then its literal input word `[start bits]`
and all leading-zero padding are unchanged. An after-oriented start would
put the state after the first variable bit and would require a separate
paid framing conversion; this helper makes no claim that such a conversion
is free. The general machine theorem itself allows any supplied normalized
initial encoding, with distinct initial and accepting states.

## 2. Exact rules

For an instruction `(q,a) -> (p,b,direction)`, write `pair=qa` if q is
before-oriented and `pair=aq` if it is after-oriented. The table below
gives all generated transition rules. Here c ranges over tape symbols.

| Direction and target orientation | Internal rule | Boundary rule |
|---|---|---|
|R, target before|`pair -> bp`|Same local rule; a missing right cell is repaired separately|
|L, target after|`pair -> pb`|Same local rule; a missing left cell is repaired separately|
|R, target after|`pair c -> b c p`|`pair ] -> b _ p ]`|
|L, target before|`c pair -> p c b`|`[ pair -> [ p _ b`|
|S, target before|`pair -> p b`|No extra rule|
|S, target after|`pair -> b p`|No extra rule|

For each distinct nonaccepting before-oriented target p of a local right
move, add one repair

    p ] -> p _ ].

For each distinct nonaccepting after-oriented target p of a local left
move, add one repair

    [ p -> [ _ p.

Do not add repairs for the accepting state. Retain the accepting cleanup
rules `accept a -> accept` and `a accept -> accept` for every tape symbol.
All rule sides are nonempty and contain exactly one state. When a bracket
occurs on a side, `[` is its first symbol or `]` its last symbol. No rule
contains `#` or crosses a boundary `][`.

## 3. Why the local and pending cases are exact

On a normalized nonaccepting configuration, the scanned symbol is fixed
by the state's orientation. If its transition is undefined, no ordinary
rewrite matches. If defined, its source `pair` is determined. In a
contextual case the neighboring tape symbol or bracket is also uniquely
determined. Therefore exactly one transition rule matches, with the
specified literal write, movement and new orientation. Repairs cannot
match a normalized configuration, because its scanned side contains an
actual tape symbol.

For example, a local right move changes

    [ l pair c r ] -> [ l b p c r ]

when a right neighbor c exists; p is now before its scanned c. At the
right edge the same rule instead gives `[ l b p ]`. This is a pending
representation with an implicit blank as p's current cell. If p is
nonaccepting, p belongs to the emitted right-repair set. The **only**
applicable rule is `p] -> p_]`: every ordinary instruction for a
before-oriented source needs a tape symbol immediately after p, and
cleanup requires the accepting state. The repair inserts precisely one
blank and restores the normalized configuration of the original right
extension. It cannot repeat because p now has a scanned tape symbol.

The local left case is symmetric. Its target is after-oriented. With a
left neighbor c, `l c pair r` becomes `l c p b r`, so p scans c. Without
that neighbor the result begins `[ p b r ]`. Every ordinary instruction
for an after-oriented source needs a tape symbol immediately before p,
so only `[p -> [_p` can apply. It restores exactly the original left
extension and cannot repeat.

Source and target orientations may differ. The six literal cases in the
table already account for that change; no additional state-swapping rule
is emitted. In the two contextual movement cases a missing neighboring
cell is supplied within the transition rule itself. Stationary moves
place the target immediately before or after the newly written current
cell, so they always preserve normalization.

The shared repair must still be present when the target's blank
transition is undefined. Repair first produces its actual blank-scanning
configuration, after which no transition applies. This is a rejecting
halt, exactly as in the original machine; an undefined blank transition
does not permit bypassing repair or inventing an accepting continuation.

If a local edge move enters the accepting state, the machine has already
accepted. The sparse configuration may omit the newly scanned blank.
The original edge rule would have inserted that blank, but accepting
cleanup would erase it. Both configurations reduce to `[accept]`, so a
repair is unnecessary. All accepting cleanup paths decrease the tape-word
length by one, preserve the accepting state, and terminate at `[accept]`.
There are no outgoing accepting instructions that could exploit this
temporary difference in explicit tape windows.

## 4. Full run and acceptance equivalence

Start from the same normalized semantic tape, encoded with the fixed
orientation of its initial state. Inductively, before first acceptance
the sparse run consists only of normalized configurations or one of the
two pending configurations above.

From each normalized state, a defined machine step is represented by one
sparse transition, optionally followed by exactly one forced repair.
After that repair its normalized semantic tape is precisely the original
machine's tape after that step. Conversely every sparse transition from a
normalized state is the matching deterministic machine step, and every
nonaccepting pending state has only its forced repair. Compressing such
two-rule pieces yields the original run. Pending acceptance corresponds
to that same final accepting machine transition; subsequent cleanup is
irrelevant to machine time and always terminates.

Thus the original machine reaches its accepting state if and only if
the sparse rewrite system reaches `[accept]`. A finite rejecting halt
stays rejecting, and an infinite sparse nonaccepting run contains infinitely
many actual machine steps: there cannot be an infinite chain of repairs
between two steps. No nondeterministic spurious branch is introduced before
acceptance. The only nondeterminism is the harmless order of accepting
cleanup.

For the default all-before scheme this theorem preserves the literal
configuration syntax as well as the initial word. It replaces each
original internal R step by one local rule, each nonaccepting right-edge
step by a local rule and its forced repair, and each accepting right-edge
step by its local rule and cleanup. Every L/S rule remains literally
unchanged. With other orientations, the theorem preserves the semantic
head position and tape through the specified encoding, not the literal
location of every intermediate state marker.

The unique-state and bracket properties also meet the hypotheses of the
[bracket-anchored word theorem](gpcp_bracket_anchored_history.md). Its row
decoder may recover a repair as one rewrite row; that is correct, since
the full sparse-rewrite acceptance equivalence has just been proved.
Compiling these rules through a numerical history is a separate task and
must rebuild its paid table, geometry and witnesses.

## 5. Rule counts and finite audits

Let t be the number of tape symbols, R/L/S the instruction counts, and k
the number of distinct nonaccepting right targets in the all-before
scheme. The old and new rule counts are respectively

    (t+1)(R+L)+S+2t,
    R+(t+1)L+S+k+2t.

The saving is exactly `tR-k`. Repairs are shared across instructions;
they are not charged once per incoming right move. For the example with
three tape symbols, three right instructions entering p and three right
instructions entering halt, the old30 rules become13: six local moves,
one repair and six cleanup rules. This is a symbolic-table saving, not a
claim of17 fewer arithmetic gates.

For arbitrary fixed orientations let ell count local moving instructions,
c count contextual moving instructions, and k_R/k_L count the distinct
nonaccepting right/left repair states. Then

    new rules = ell+(t+1)c+S+k_R+k_L+2t,
    old rules - new rules = t*ell-k_R-k_L.

Every repair state has at least one matching local incoming instruction,
so `k_R+k_L <= ell` and the count does not exceed the original rule count.
The exact orientation choice is fixed compiler data; no globally optimal
table or arithmetic circuit is asserted.

The checker compares every source/target orientation, move direction,
read/write symbol and boundary case on tape alphabets of sizes1,2,3
with an independent bounded-tape step and the old context-enumerated
rules. It separately checks long right-then-left computations through
length96, partial blank-transition rejection, pending acceptance, and
64 successive right or left blank repairs in nonaccepting loops.
Random fixed machine tables vary shared targets, transition gaps and
state orientations. All bounded accepting cleanup orders are checked to
terminate at the same bracketed accepting word.

These finite comparisons audit the implementation; the run argument
above proves the theorem for arbitrary deterministic tables and unbounded
durations. No native Pell witnesses, arithmetic compiler bound or universal
machine theorem is inferred from the finite fixtures.

```sh
python sparse_tm_rewriting.py
```
