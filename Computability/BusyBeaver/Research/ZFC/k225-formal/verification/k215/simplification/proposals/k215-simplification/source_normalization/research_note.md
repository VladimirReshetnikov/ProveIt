# K215 source-certificate normalization

Baseline: `VladimirReshetnikov/ProveIt` commit
`b6c7087477e51c017003bd729e712c8969733223`.

## New result

The pinned source correspondence certificate has 2,240 entries, all at offset
zero. It distinguishes instruction pointers that differ only by trailing zero
bits. Wade's path semantics reads omitted bits as zero, so these pointers give
the same leaf observation and the same next small step for every register file.
Quotienting this representation redundancy gives **1,426 entries**, removing
814 entries, or **36.3393%**, without changing either program or any machine
transition. There are 1,425 decrement entries, one halt entry, and 2,851 branch
obligations including the initial branch.

The `normalize_certificate.py` generator independently reconstructs the old
certificate from the pinned input data, constructs the new certificate, checks
every local branch, serializes it, reads it back, and checks it again. It also
emits the explicit surjection from all 2,240 old entries to the 1,426 new entries
and verifies that this surjection preserves both successor indices. The new
JSON certificate is 78,623 bytes; its largest pointer has 176 bits. Its balanced
Lean certificate declarations occupy 106,089 bytes versus 197,044 bytes for the
pinned offset-certificate section, including that section's small footer. The
state-count result is unchanged at 215.

The new **generic semantic checker** is implemented in
`RMNormalizedBisim.lean` (161 lines). Lean 4.32.0 successfully checked its
`check_halts_iff` theorem against the pinned `RegisterPath`, `RMDag`, `RMEquiv`,
and `RMBisim` modules. The reported assumptions are `[propext, Quot.sound]`.
There is no `sorry`, no admitted statement, no consistency hypothesis, and no
native evaluator axiom. This is a new checker theorem, not an assertion that a
Python success alone certifies the complete machine.

The **concrete source-program instance is now also kernel checked**. All 1,426
entries and the initial branch pass, and the final facade exports the original
`KSource215.p215_halts_iff` statement for every register file. Its only reported
axioms are `[propext, Classical.choice, Quot.sound]`. The concrete checking uses
16 balanced certificate batches; the later eight are each divided into four
small internal proofs to limit peak memory. The final receipt binds all 22
local Lean modules to successful checks and pins their eight upstream
dependencies. These checks were completed in an incremental isolated build;
the supplied driver reproduces the entire 30-module minimal import closure
from an empty directory. This is the exact source-correspondence theorem, not
a fresh build of the whole machine-to-consistency endpoint.

The summary's `kernel_checked: false` describes the Python producer, which
performs no kernel checking. `kernel_receipt.json` records the separately
completed Lean checks and has `kernel_checked: true`. The two fields have
explicitly different scopes.

## Mathematical proof

For a finite bit list P, let bit(P,i) be its ith bit, with false outside the
list. Write P ~ Q when bit(P,i) = bit(Q,i) for all natural i. This is exactly the
repository's existing `RMEquiv.ipeq`, not a new machine semantics.

The repository already proves `walk_ipeq`, `step_ipeq`, and `hn_ipeq`. The new
lemma `tsite_ipeq` combines `walk_ipeq` and the zero-padded prefix lemma
`pre_ipeq`: the decoder's entire observation `(instruction, consumed path)` is
equal on equivalent input pointers. In particular, it identifies both the
instruction and the actual finite path on which break/continue arithmetic acts.

Suppose a finite certificate denotes a relation S between representative
pointers. Saturate it as

    S*(P,Q) iff there exist A,B such that S(A,B), P ~ A, and Q ~ B.

The new Boolean comparator `ibeq` checks ~ directly. When one list runs out,
the unmatched suffix of the other must consist entirely of false bits. Its
soundness theorem `ibeq_ok` is a structural induction on the lists. No bound on
register values or machine runtime appears.

The branch checker still executes exactly the existing `seg` function, with
the same fuel, and still checks that both segments increment each register
equally often. The only alteration is that the resulting pointers must be
equivalent to their certificate representatives, instead of literally equal.
Consequently a checked branch satisfies the original `BranchGood` definition
for the saturated relation S*.

At a stored representative, the entry checker verifies exactly the original
halt/decrement alternatives. At an arbitrary member of S*, `tsite_ipeq`
transports those observations to the representatives. Thus the same entry
obligation holds everywhere in S*. These two facts construct an instance of
the existing `RMBisim.Bisim`. Its existing `halts_iff` theorem then gives

    Halts p215 ([],R) iff Halts pathDagPerm ([],R)

for every natural-valued register file R. No new simulation induction, no
offset arithmetic, and no reverse certificate are required.

### A subtlety the implementation preserves

Normalizing a stored pointer does **not** authorize performing `breakPath` or
`incPath` directly on the normalized list. Path arithmetic acts on the consumed
leaf path returned by `tsite`, exactly as in the original semantics. Both the
new Lean checker and the Python generator use that consumed path. Deleting an
arbitrary suffix, or shortening the physical binary instruction-pointer region
without a tape-frame proof, would be an unjustified transformation. This work
does neither.

## Reproduction and integration

The scripts operate on pinned `sites215.json` and `dagperm_nodes.json`. The
upstream `gen_cert.py` is retained with provenance; it reconstructs the old
untrusted certificate and supplies the existing path interpreter. The new
checker uses the repository semantics directly and does not trust this Python
interpreter or the generator.

The recommended formal integration preserves the public names `p215`,
`pathDagPerm`, `path_iff_iter`, `t215`, `tD`, and `p215_halts_iff`, allowing the
machine endpoint to remain unchanged. The supplied thin `KSource215` facade imports the
new normalized checker batches and exports the identical public source theorem.
Keep the old certificate files for historical reproducibility but remove them
from this endpoint's import closure.

For a true Rocq port, carry the same saturated relation into its existing
segment-bisimulation checker and replace literal path equality by zero-padding
equality. The proof is the same: observation congruence plus the old simulation
theorem. Reusing the same JSON certificate and its input hashes makes the two
lanes auditably describe the same finite obligations. A Rocq data rendering
alone is not a kernel-checked Rocq source theorem.

## Reproduction resource issue and its remedy

During the fresh rebuild, the pinned `KSource215Data` could not be checked in
the available memory. Isolating its first program-only section localized the
problem to `wfCheck222`: a single kernel evaluation checks 487 nodes against
three linked-list tables. That isolated check exceeded a 3.5 GB kernel limit.
This is a local reproduction failure, not a refutation of the repository's
recorded successful build.

`render_programs.py` preserves the exact programs, tables, and statement of
`wfCheck222` but checks its finite universal condition in sixteen batches (15
of size 32 and one of size 7), joining them with arithmetic. This introduces no
trusted computation. `render_shared_trees.py` additionally preserves decoder
sharing: it names the 179 source DAG nodes and the 261 target DAG nodes reachable
from its root, instead of pasting the expanded 4,751-leaf trees twice. Each tree
has a local bottom-up fuel theorem. Both modules passed the Lean kernel. The final program/WF check used
2,297,208 KiB peak RSS; the shared-tree check used 783,508 KiB. These resource
improvements are distinct from the reduction in certificate entry count.
The supplied generated source has more local lemma declarations, so this is
not presented as an across-the-board reduction in proof lines.

## Alternatives considered

A further experiment builds the finite graph of decrement/halt checkpoints
with branch increment vectors, then computes its largest stable bisimulation
quotient. Each normalized program has 1,426 reachable checkpoint states. The
combined quotient has 1,423 classes, a saving of only three additional classes.
That experiment is Python evidence, not a new kernel theorem. It suggests that
the inexpensive path normalization captures almost all compression available
from this particular graph abstraction. Introducing an additional graph
semantics and its compiler theorem is not presently justified by three classes.

Larger future reductions should instead expose reusable arithmetic subroutine
contracts with their exit behavior. Identical DAG nodes cannot simply be
merged regardless of context: `break` and `continue` carry relative exit levels,
and distinct callers can supply different continuations. A future macro proof
must preserve those interfaces explicitly.

## What the current baseline already simplified

The phase3 record at this pinned commit already includes a general enumerator
theorem for valid states between proof candidates; guarded rho8 schemas and a
small deduction theorem replacing repeated valuation substitution; a smaller
site-coverage facade; direct AX atom effects; selector-level lemmas; and
symbolic command-block execution. These are existing work, not contributions
of this note. The current endpoint closure is reported as 185 Lean project
modules, although the older fresh-build record contains 204. The source-path
normalization above is a distinct new reduction.

## Source references

- `Computability/BusyBeaver/Lean/BusyBeaver/ZFC/RegisterPath.lean`:
  `bit`, `consume`, `execute`, `step`, and the exact halting semantics.
- `.../RMEquiv.lean`: `ipeq`, `pre_ipeq`, `walk_ipeq`, `step_ipeq`,
  `hn_ipeq`, `wfCheck`, and `wfCheck_sound`.
- `.../RMBisim.lean`: `tsite`, `seg`, `BranchGood`, `EntryGood`, `Bisim`,
  and the reused `Bisim.halts_iff` theorem.
- `.../KSource215Data.lean`: exact source program, target program interface,
  and the 2,240-entry pinned offset-zero certificate.
- `Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/`
  `simplification/phase3/README.md`: prior simplifications and current closure.
