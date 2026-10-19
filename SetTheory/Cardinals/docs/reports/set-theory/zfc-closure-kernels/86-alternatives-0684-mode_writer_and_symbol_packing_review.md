# Independent review: fixed-width mode writer and symbol-partition packing

Date: 2026-10-18. Reviewed inputs in `../native_copier`:
`anchor_mode_writer.py`, `anchor_mode_writer_guards.json`, and
`SYMBOL_PARTITION_PACKING.md`. Exact hashes are in
`anchor_mode_writer_independent_audit.json`.

## Verdict

The 11-state writer's full-tape, seven-step contract is valid. Its four
forced-one states are exactly `unseen4`, `seen0`, `seen1`, and `seen2`.
The claimed complete 16-case guard certificate matches the literal table.

The global symbol-partition quotient theorem is also correct. **No additional
incoming-edge restriction is required.** One must prove the read guards for
the original complete composition, project every transition target and entry,
and leave the genuine halt distinct. For separately audited modules with
multiple terminal ports, keep the terminal distinctions unless they have been
properly linked into the complete machine. Component-local guards cannot be
assumed for arbitrary new callers.

## Writer theorem and ordinary proof

For old mode j and desired mode k in {1,2,3,4}, the seven-cell header has zeros
exactly at positions j and 6 and ones at the other five positions. Enter at
position 0 in state `unseen{k}`. The desired output has zeros exactly at k and
6. The entire tape outside these seven cells is arbitrary.

All enabled operational transitions move right. Consider the three cases:

- k=j: the initial countdown crosses k ones. `unseen0` reads the old separator
  zero, leaves it zero, and `final_zero` passes the remaining ones to the final
  zero at position 6, which is preserved before return.
- k<j: the countdown reaches position k before the old separator. `unseen0`
  replaces that one by zero. `old_zero` passes intervening ones and replaces
  the old separator at j by one. `final_zero` then reaches the preserved final
  zero at 6.
- k>j: at position j the countdown state is `unseen{k-j}` with 1<=k-j<=3.
  It replaces the old separator by one and switches to a `seen` countdown.
  Every cell until k is one because the only interior old zero was at j.
  `seen0` replaces the one at k by zero; `final_zero` then reaches position 6.

Thus exactly positions 0..6 are read, each once, and only the two intended
separator positions can change. Every case returns after exactly seven moves
with head at position 7 and the correct header. Translation proves the result
at every tape origin, and no exterior condition is needed.

`unseen4` occurs only initially for desired k=4, where the header's first cell
is one. Every `seen` state occurs after consuming the unique old interior
separator, and before reaching the still-interior new separator, hence reads
one. These prove the four read guards universally. The other six operational
states genuinely have both read symbols across allowed header cases; the
reject state is unreachable under this component's valid contract.

The writer has 10 operational states plus reject, 22 rows, and separate return
11. Its four entries already encode the desired mode in control. Acquiring that
mode and positioning the head at the header are still charged caller duties.
At exit the head is immediately after the fixed seven-cell header, not at an
arena marker. The return-to-caller routing must also be implemented and charged.

## Precise reusable packing theorem

Let M be a deterministic binary TM with working states Q and a distinct halt H.
Let I be the permitted initial configurations, possibly with multiple entry
states. Suppose a proved invariant R holds initially for every C in I and is
preserved by every nonhalting original step. For each working q, let
A(q) be a subset of {0,1}; require that R(C) and state(C)=q imply that C's
scanned symbol belongs to A(q). This includes each permitted initial entry,
internal loops and every later invocation, not merely the first call.

Choose a **disjoint matching** between states with A(q)={0} and states with
A(q)={1}. Let pi merge each pair, keep all other states distinct, and satisfy
`pi(H)=H'` and `pi(q)!=H'` for every working q. Define the quotient table:

- for a paired class, use the projected zero row of its forced-zero member and
  the projected one row of its forced-one member;
- for an unpaired state, project both of its original rows;
- in every row preserve the written bit and head movement, and project the
  target through pi.

Map every entry state through pi; retain the original tape and head. Then for
every C in I, at every original execution step n, the quotient configuration
is exactly `(pi(state_n), head_n, tape_n)`. In particular both machines halt at
exactly the same time, or both run forever; complete tapes and heads agree.

**Proof.** At step zero this is the specified projected entry. Suppose the
configurations correspond and the original state is working. Its invariant
selects an allowed read symbol. If its class is paired, that symbol selects
exactly the row belonging to the original member. If unpaired, its row is
unchanged apart from the target projection. Either way the two steps write
the same bit, move identically and have projected next states, establishing
the induction. The original next configuration satisfies R by hypothesis.
If the original is halted, so is its image. Conversely a projected configuration
can be halted only if the original is halted, because H is the unique preimage
of H'. This proves exact halting-time equivalence as well as the full trace.

The proof places no restriction on which original states enter a paired class.
Even newly appearing quotient self-loops are harmless: each next scanned symbol
is guaranteed by the original invariant and selects the correct role. There is
no need to assume the quotient's guards in advance; they follow from this
simulation relation. What is necessary is redirecting **all** targets and
initial entries, rather than merely copying two rows into one retained state.

If the original invariant and entry facts are proved in ZFC, this finite-step
induction is a ZFC proof of the exact halting equivalence and can be composed
with the existing consistency calibration. No PA endpoint is needed.

With n0 forced-zero and n1 forced-one states, this matching saves min(n0,n1)
working states. This is a guaranteed saving for this construction, not a
claim of optimal compression. States with empty read domains are simply
unreachable on I; the stated theorem need not delete or merge them. A shared
failure sink needs its own compatible semantics, as the original document says.

## Terminal ports and composition boundary

A component's RETURN is not automatically the global halt. Apply the theorem
after connecting returns to their real continuations, or keep all distinguished
terminal ports separate and prove the analogous multi-terminal statement.
Merging a success port with a reject port or an ordinary working state is not
licensed by the single-halt theorem. Likewise a reject state that is unreachable
on one module's valid calls may be reachable elsewhere in a complete candidate
checker, so its read domain must be recomputed for the global invariant.

For the template oracle, all leaf-emitter reads are forced zero under the
**genuine complete leaf path followed by at least three untouched zero cells**
entry contract. Each emitter reads a fresh cell to its right; earlier writes
cannot change that cell. The oracle's broader previously reviewed contract
allowed arbitrary emitter-input bits, and that broader contract alone does
not justify this packing. Every full-runtime caller must establish the narrower
zero-padding premise at the actual call time. A prefix that stops before the
true leaf, or unused path bits after that leaf, need not satisfy it.

Consequently pairing four of those guarded emitter states with the writer's
four guarded forced-one states is mathematically permitted for any matching
once the complete old composition and its guards are proved. There is no
certified complete composition or new total-machine state count merely from
listing these complementary local roles.

## Independent executable evidence

`audit_anchor_mode_writer.py` parses the emitted table, checks all 22 rows
against the compiler, independently represents headers by their zero positions,
and performs 3,072 full-tape tests across all 16 old/new modes, three translated
origins and every pattern of three adjacent exterior bits on each side. Every
run takes exactly seven right moves and preserves all exterior cells.
All 16 saved traces and the complete allowed-read map were independently
verified against literal transitions. Because the contract has exactly 16
local input/control cases and no exterior read occurs, this exhaustive finite
certificate proves its component guards for arbitrary exterior tapes, not
merely for a bounded sample of source parameters.

Table SHA-256:
`6d3c5387b7f8dc5b14138337b09462a75e6739ebb6f9071127aa8c299666525f`.
No producer file, shared source, external repository, or user computer was
modified during this review.
