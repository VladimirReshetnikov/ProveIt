# Composing register boxes with an existential spare suffix

## Scope and source contracts

This is an ordinary mathematical proof of the stronger certificate boundary
used in the current search. It does not claim a surviving smaller machine.
Its four physical box lemmas are the already proved marking, increment,
zero-decrement and positive-decrement excursions, instantiated on a table
whose protected support rows remain unchanged. Their detailed whole-tape
interfaces are documented in `register_mark_increment253.md`,
`register_boxes253.md`, `register_decrement253.md`, and
`permutation252_frame.md` at pinned ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38`.

Let `bits(v)=0 1^(v+1)`. The complete unmarked right file contains the nine
primary values in physical order followed by an arbitrary finite spare list
S, then a blank exterior. The physical spare list is distinct from unused
logical registers. Selected indices must be below nine.

The known contracts give exact machine runs, with arbitrary primary values,
arbitrary S (including nonzero entries), arbitrary finite left context and
integer head. Marking erases the selected block's first one and remembers
which index is selected. Increment restores the marker and increases the
selected value by one, preserving S. A zero decrement restores the marker
and leaves all values and S unchanged. A positive decrement restores the
marker, decreases the selected value by one, and changes S to `S ++ [0]`.
The last spare must not be silently omitted at the physical level.

The physical return states and one-cell head displacement are part of each
contract. Mark's return state is not increment/decrement's entry state. Any
intervening control/positioning steps have to be verified by literal symbolic
execution; the abstract operations are not permission to connect unmatched
physical endpoints.

## Box-composition lemma

Fix an initial primary vector R in N^9, initial spares S, and any path through
a symbolic execution certificate. Maintain an integer vector delta, initially
zero; an integer d>=0, initially zero; and an optional marked index. The
certificate's plain file denotes primary vector `R+delta` and spare list
`S ++ replicate(d,0)`. A marked file has the same values, except the selected
block's first unary one is erased. Every component of `R+delta` must remain
nonnegative.

Apply the following updates:

| Validated box | Required condition | New ledger |
|---|---|---|
| mark r | Plain file; 0<=r<9 | Marked index r; delta,d unchanged |
| increment r | Marked r | Plain; delta_r := delta_r+1 |
| zero decrement r | Marked r; R_r+delta_r=0 | Plain; delta,d unchanged |
| positive decrement r | Marked r; R_r+delta_r>=1 | Plain; delta_r := delta_r-1; d := d+1 |

Then every finite path obtained by composing valid physical box excursions
and exact literal/scan steps has precisely the tape semantics asserted by
its symbolic ledger. In particular, an unmarked terminal ledger with net
delta equal to the required source-instruction effect represents exactly
those primary values, even when several operations have canceled.

Proof: induction on the certificate path. Literal steps use the actual
transition table. A justified scan is the finite iteration of its loop row
and preserves the entire symbolic tape description. The four box cases are
their whole-tape contracts, applied to the current `R+delta` and current
spares `S ++ replicate(d,0)`. All guards concern the *current* value. Positive
decrement gives
`(S ++ replicate(d,0)) ++ [0] = S ++ replicate(d+1,0)`.
Natural nonnegativity follows from the decrement guard; increments preserve
it. No operation selects a spare. Associativity of finite-run composition
concatenates the exact physical witnesses, including their head coordinates
and return states. This proves the induction claim.

This proof justifies any finite number of operations, not only one effect
per instruction. For example, increment followed later by a justified
positive decrement can have net primary effect zero while appending a zero
spare. Such a path was outside the old single-effect checker.

If a guard is not determined, the checker may split into the cases
`R_r+delta_r=0` and `R_r+delta_r>=1`. These are exhaustive because current
values are natural. Infeasible branches may be discarded only with a sound
constraint contradiction. Fuel exhaustion or an unsupported symbolic rule
is not an infeasibility proof and is not a correctness certificate.

## Why arbitrary final spare suffixes are enough

For a logical source configuration u, define `Frame(u,c)` to mean that there
exist an admissible integer head, gap and finite spare list S for which c is
the complete physical dispatch frame of u. Admissibility includes:

* the exact dispatch state and source PC encoding;
* the correct full left context, header, gap constraint and blank exterior;
* the nine primary values in the fixed register-permutation order;
* an arbitrary finite S, not identified with any logical register.

The final S is existential. Thus extending it by any finite zero suffix
preserves the form of `Frame` and the hypothesis needed for every subsequent
register box. This is not equality of the two tapes, and it is not a claim
of one-step binary bisimilarity. It is an invariant relation to the same
logical configuration.

Once the next-state/next-PC and nine primary values match, the spare-growth
ledger may be forgotten at a dispatch cutpoint. It has already justified the
physical tape; the next macro proof starts with the new arbitrary S. This
removes a real overconstraint in comparisons that insist on the reference
instruction's exact spare suffix.

## Reachable-invariant macro simulation theorem

Use the following terminal-event convention. The maintained `RegisterPath`
semantics defines `Halts` by reaching a configuration whose decoder selects
`CH`; executing `CH` is not a successful `RegisterPath.run` step. Adjoin a
fresh terminal state H and one transition from each `CH` configuration to H.
Reaching H has exactly the same halting predicate, while counting that last
terminal event as one step. Thus a source prefix reported as ending in its
`CH` event has one fewer successful steps in the original `RegisterPath.run`
clock. Break and continue each count as one successful step; decoder-tree
traversal counts as none. All block clocks below use the adjoined terminal
transition convention.

Let P be the deterministic source program on a finite control graph and
natural-valued primary registers, **total on every nonhalting configuration**
in its admissible domain. The adjoined terminal state H is halting. Let
I_s(R) be a predicate per control site. Suppose:

1. The concrete blank bootstrap reaches `Frame((s0,R0),c0)`, and I_s0(R0).
2. I is inductive: every enabled source transition from I_s(R) either halts
   or reaches (s',R') satisfying I_s'(R').
3. For every site s, every R satisfying I_s(R), every admissible complete
   input frame and every enabled source guard, a finite validated symbolic
   macro certificate takes the *modified* binary machine to a frame of the
   actual source successor (or to the actual halt state), in a positive
   number of binary steps.
4. Nonhalting macro paths contain no earlier binary halt. This is automatic
   from an exact running endpoint when the machine semantics make halt
   absorbing, but must be checked under any other convention.

Then the modified binary machine halts from blank iff P halts from (s0,R0).

Proof, source-to-binary: induct on the number of source transitions in a
finite halting run. Inductiveness supplies the next invariant premise, and
the macro witness supplies the next whole frame. Concatenate the positive
finite runs and the bootstrap. The final macro halts the binary machine.

Proof, binary-to-source: suppose the source never halts. Recursively choose
the deterministic source successors and their finite positive macro runs.
Their concatenation is the unique binary run after the bootstrap. After n
macros the accumulated binary time is at least n, so every finite binary
time lies before some macro endpoint. Each finite prefix is nonhalting by
(4), so no binary halt is possible. Contraposition proves the implication.
All this is ordinary induction/recursion on omega, formalizable in ZFC.

The theorem also follows constructively by induction on a purported binary
halting time: each positive macro consumes at least one time unit, allowing
a finite source-prefix bound. No assumption of consistency or nonhalting of
the original machine is used.

## Specialization by finite abstract invariants

An abstract invariant certificate supplies each I_s. It is enough to check
initial inclusion and every finite source transfer edge. The check must use
unbounded meanings of register classes. For example, mask `{0,1,>=2}` and a
closed difference-bound matrix describe infinitely many natural vectors.
The finite abstract certificate is proved sound by induction on source
steps; it is not a finite sample of concrete computations.

At a box test, a register other than the syntactic source instruction's
tested register may be known zero from I_s. Applying its zero-decrement
contract is sound and preserves the entire current frame. The old checker
allowed only the original named guard, so it missed this possibility.
Repeated zero tests are also safe. If operations have changed registers,
the predicate must be applied to `R+delta`, rather than the original R.

Initial/source phase restrictions must not be imposed on arbitrary prepared
binary configurations. The theorem is about the reachable run covered by
the verified bootstrap and inductive invariant. Every candidate still needs
its own blank bootstrap and its complete applicable macro-certificate set.

## Consequence for ZFC calibration

The original source program's halting/refutation equivalence is unchanged.
Composing the macro simulation theorem with the source's native/ZF/ZFC
calibration yields a ZFC-formalizable nonhalting/Con(ZFC) equivalence for any
new table satisfying the above certificates. No new logical calculus,
irreducibility assumption, PA totality claim, or consistency assumption is
required. Until a candidate passes those obligations, this is a rigorously
justified larger search space, not a smaller consistency machine.

## Extension: adaptive finite positive source blocks

Exact one-instruction synchronization is unnecessary. The macro certificate
may end at any verified state obtained after k>=1 source steps, where k is
finite and may depend on the source state, its enabled guards, and the
certificate branch. Its binary execution length t must also be positive.
All intermediate source steps must be the actual deterministic source
semantics, and the source invariant must hold at the resulting endpoint.

A live endpoint is permitted only when no source halt has already occurred
in that block. Equivalently, define halting as absorbing and require a live
source configuration at the endpoint. A source halt endpoint must match an
actual binary halt; it cannot be treated as another dispatch frame. These
conditions also apply to early halts on the binary side.

Under those conditions, the same blank halting equivalence follows. To
prove it, iterate the block witnesses. After n blocks, source progress is at
least n and binary progress is at least n. If the source halts after N
steps, then within at most N blocks the reference path reaches or passes
that halting time. It cannot have a live endpoint past that time, so the
corresponding block has a halt endpoint and the binary machine halts.
Conversely, if the source never halts, every block ends live. The binary
times of those live endpoints are unbounded, and every finite prefix is
nonhalting; therefore the binary machine never halts.

This is a positive block simulation. It permits different program-counter
representations and extra source operations *within* a macro, while still
requiring the exact PC, primary values and admissible physical frame at its
chosen synchronization endpoint. It supplies no permission to identify two
unrelated continuations merely because their next instructions look similar.

A finite search over several candidate reference endpoints is sufficient:
any successful endpoint must carry its own verified positive source prefix
and its own full binary symbolic contract. Failure to find such an endpoint
within a chosen source-step or binary-fuel limit is only a search failure.
