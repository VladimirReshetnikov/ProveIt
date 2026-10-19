# Independent review of the fold proof checker

The reviewed checker is `root_verification/verify_state_fold.py`. The final
root package records its delivered hash. This branch did not edit it.

## Findings and repairs

Two genuine generic soundness gaps were reported and repaired by root:

1. The deleted state was not required to be an old working state. Supplying
   `drop=254` could map the old halt symbol to a live state and let an ordinary
   live endpoint certify an old halting row. The repaired checker requires
   `drop` to be an old working state and `keep` to be a distinct new working
   state. These guards keep the halt symbol fixed.
2. If the initial old state was the deleted state, a nonempty tag transform
   could flip the initial input tape while the old initial validation checked
   only state and head. The repaired checker rejects that case. Together with
   the existing initial state and head checks, its initial configuration map
   now preserves the whole input tape.

Neither issue applied to the actual known `235 -> 98` replay. Both have small
adversarial examples in `check_fold_checker_regressions.py`: the old machine
halts on blank tape in one step, and the new machine provably loops on the
same blank tape. The repaired checker rejects both proposed maps. The script
checks those concrete machine behaviors independently of the checker.

A separate receipt-provenance issue was reported and repaired: hashing table
paths after proof construction, separately from their parse-time reads,
could attach the hash of concurrently replaced bytes to a proof about earlier
bytes. The repaired main routine captures each table's bytes once and both
parses and hashes that same byte string. This was a generic race concern
found during source review; no such replacement was observed in the run.
The repaired checker hash is
`43c89550f165972cefa619993084b53e10e5d31165d152749ecc3a2144c4044e`.

## General logical soundness after the boundary guards

**Inductive bit facts.** `None` denotes an unreachable state; a dictionary
denotes the conjunction of its finite relative bit facts. The initial state
has the empty conjunction, allowing every input tape. A transition writes
its literal bit and translates offsets by its head movement. Joining incoming
states intersects equal facts, weakening the abstract condition. Once a state
has been reached its fact set can only shrink. The resulting finite fixed
point is independently rechecked against every row whose precondition is
consistent with the current read. This last check gives an ordinary
inductive invariant, including the unreachability assertions.

**Symbolic input tapes.** Every unmodified cell is represented by its own
input variable. The optional tag XOR affects just one such cell; writes
replace expressions by literal bits. Reading an unknown input variable
branches on both possible values and extends the partial assignment
consistently. Reading a known variable or constant has one branch. These
branches partition all tapes satisfying the starting row's invariant and
read bit; there is no sample-based generalization.

**Whole-tape equality.** At each proposed endpoint, the union of written
cells, the old write cell, and the possible target tag cell contains every
position at which the two represented tapes can differ. All other cells
remain the same input variable. The checker tests equality of expressions
at every position in that finite union, together with the mapped state and
exact head position. It therefore establishes equality of the entire tape
at every live endpoint.

**Halting and positive blocks.** An accepted block always has at least one
new transition. A halted new state before a live old endpoint is rejected.
An old halting row may terminate at the new halt symbol with any final head
or tape. That relaxation is sound for halting equivalence, and does not
preserve a final score or exact terminal configuration. A proof statement
must retain this distinction.

**Unbounded simulation.** Starting from any common input tape and head,
induction on the old run supplies consecutive accepted new blocks. The
inductive invariant supplies each old row precondition. Finite old halting
therefore gives finite new halting. If the old run is infinite, the strictly
positive block lengths have unbounded partial sums, and every covered new
time is active. Determinism makes this the actual new run, so it cannot halt.
No global simulation time limit is used: fuel and branch caps only bound the
attempt to find a finite local proof.

No further logical flaw was found in these mechanisms. The source audit is
an ordinary mathematical review; it is not a proof-assistant formalization
of the Python interpreter or of the checker implementation.
