# Rocq macro-proof transport for K215

Baseline: `VladimirReshetnikov/ProveIt` at
`cbf94cb552a3b49509e0eee80e7455d4eb5974c6`.

## Result

The current K215 `ProgLibPerm.v` repeats the K218 `ProgLib219.v` development.
After removing nested comments and whitespace and consistently renaming the
namespace/program identifiers, their complete source token sequences are equal.
The new static census locates 58 concrete-node macro lemmas with 53 distinct
entry nodes. Their common transitive node footprint has only 89 nodes, and the
two literal programs agree on every node in that footprint.

This packet supplies a checked transport theorem for exactly that footprint.
It proves, for every listed entry node `n`, every initial register function
`R`, every exit `x`, and every final register function `R'`,

```text
run dag219 (ENode n) R x R' <-> run dagPerm (ENode n) R x R'.
```

The equivalence preserves normal returns, breaks, continues and halts, as well
as the exact output registers. It is stronger than preservation of successful
halting alone. There is no bounded-execution premise, well-formed-formula
premise, register bound, consistency premise or additional axiom.

## Why the local theorem is enough

For a finite set `S` of node labels, the interface `closed_agreement p q S`
requires two facts for each member:

1. Both programs have the identical pair of outgoing edges at that node.
2. Every outgoing node edge points back into `S`.

Primitive register operations are shared by the existing `K230.RM` semantics.
Induction on a finite big-step derivation therefore transfers every constructor.
The loop constructor transfers its car, cdr and recursive restart derivations;
no structural acyclicity or termination assumption is needed. The symmetric
agreement gives the converse. `check_footprint_sound` proves that the executable
finite checker establishes these hypotheses. Its 89-node instance is reduced
inside Coq using `vm_compute`.

The changed old nodes are `139`, `141`, `147` and `236`; K215 additionally has
nodes `467` through `486`. None belongs to the common macro footprint. This is
why equality, pairing, unpairing, constructor, register-transfer and fetch
macros can all be inherited while K215's command dispatch and axiom block keep
their specialized proofs. Of the old `atoms` list's 47 roots, 46 transfer;
dispatch node `141` is the exception. The 58 concrete lemma census includes
internal helper roots as well as the public atom roots.

## What this would simplify in production

Move the shared register record, `get`, `set`, `approx`, and generic `sem`/sequence
rules to a common module. Retain the old public names through explicit aliases.
Prove the macro library once and derive the K215 contracts with `macro_run_iff`
or its `macro_contract` corollary. Keep the dispatch, changed axiom sequence and
root correctness theorem separate. Update the producer rather than modifying
only its generated output.

One implementation can import the old macro proofs and wrap them. A better
long-term dependency boundary is a common macro module parameterized by its
finite table contract, or a canonical 89-node macro table. This avoids making
K215 depend on an entire earlier machine development merely to reuse unchanged
macros. The current old/new `St` records are separately declared; sharing or
explicitly translating those records is a real integration task. The pilot
deliberately works at the already shared raw-register semantics, where the
transport has no representation ambiguity.

This is a source-sharing and maintenance proposal. It does **not** establish
that the selected K215 transitive source closure becomes smaller: replacing a
local proof by an import can keep the same proof body in the closure and add
wrappers. Measure both selected closure and total maintained source plus
generators after integration. In particular, the 780-line K215 macro library
cannot simply be counted as 780 removed lines while ignoring its shared
replacement. The existing Lean `RMTransfer`/`L2Perm` approach is the architectural
precedent; this contribution is a checked Rocq adapter and the concrete K215
footprint, not a claim that program transport is a new mathematical principle.

## Checked scope

`build-attempt1/receipt.json` records a successful isolated build with **Coq
8.18.0, OCaml 4.14.1**. Five modules were compiled from source: the retained
`K230.RM` semantics, the two literal current DAG files, `RunTransfer.v`, and
`Footprint215.v`. The three generic theorem reports and two concrete theorem
reports are all closed under the global context. Recursive
`coqchk -silent Footprint215` exited zero. Source, object and log hashes are
recorded. No source compatibility edit was needed for these five files.

This is not a fresh check with the repository's designated Rocq 9.1.0/stdlib
9.0.0 toolchain, and it is not a rebuilt machine-to-ZFC endpoint. Production
adoption still requires API compatibility, producer replay, affected downstream
compilation and the exact endpoint assumption/checker gates under that
designated toolchain. The repository's existing physical machine and source
tables are unchanged.

Reproduce the static census:

```sh
python3 snapshot_audit.py --repo /path/to/ProveIt --out snapshot_audit.json
```

Reproduce the focused kernel check:

```sh
python3 check.py --deps-root ./deps \
  --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /path/to/new-empty-check-directory
```

The three exact source dependencies are included under `deps/`, so this
kernel check does not need a repository checkout or network access. Alternatively,
replace `--deps-root ./deps` with `--repo /path/to/ProveIt` to verify the same
proofs against the pinned repository files. The static macro-library census
above still needs the repository because it examines the full two macro libraries
and historical receipts, which are not duplicated in this packet.

The driver requires exact source SHA-256 pins, uses a fresh output directory,
and checks all subprocess exit codes and the expected closed assumption reports.
Its original successful run used the repository route. The later vendored route
only changes source-path resolution; the proof sources, dependencies and compiler
commands remain unchanged. It never edits the repository. Compiled objects and
toolchain binaries need not be distributed.

## Other measured Rocq opportunities

The current extension carries eight variant copies each of `Runtime230Core.v`,
`Interpreter230Sites.v`, `Sim230.v`, `Tape230Blocks.v` and `Tape230Carry.v`.
Their K215 copies contain respectively 19,622, 8,121, 12,037, 8,786 and 5,579 bytes.
`Runtime230Core` already takes four register-excursion theorems as hypotheses;
its remaining table dependence can be made explicit in a shared module.
`Sim230` can similarly be parameterized by the checked program, boot register
file, tape frame and site-correctness contract. These are larger integration
steps than the exact macro transport, and this packet does not claim to have
implemented them.

The positive-progress bit in the symbolic executor must survive any refactor.
`sstep_sound` permits administrative zero-step transformations, while
`exec_sound` proves a positive concrete run when called with `moved = false`.
The outer `Sim230Main.tm230_rm` proof uses `progress_halts`; replacing positive
progress by a merely reflexive/transitive simulation would invalidate the
halting-reflection argument.

## Evidence boundaries

The historical `normalized-91` receipt has 44 compiled entries. The current
`coq/215` directory has 43 source files, and ten of the receipt's entries have
different current hashes or are absent. The census records the exact differences.
That does not refute the historical check or the machine's established result;
it means that receipt alone does not certify the current modified source bytes.
The current generic implication core and direct block compiler should not be
silently described as the earlier checked replay/decoder-based implementation.

Historical normalized-91 timing lists `ProgLibPerm` at 128.54 seconds,
`Boot230` at 81.02, `Interpreter230Check` at 78.27, `Sim230` at 38.40,
`L2RootPerm` at 28.64 and `MainPerm` at 28.59. These are useful prioritization
data for that earlier run, not current-toolchain benchmarks or estimates of the
speedup from this pilot.

The mathematical calibration and exact binary-table correspondence remain
separate obligations. The repository's verification page explicitly distinguishes
its external proof-assistant theorems from an internal PA proof or a derivation
encoded in ZFC's own proof syntax. This transport pilot does not close that
separate internalization task.

## Attribution

The underlying machine, register semantics and macro specifications are inherited
from ProveIt and its credited Elliot Glazer / Jeff constructions. The literal
tables and macro proofs retain their repository source identity. New files here
are the finite-footprint adapter, its concrete instance, the audit/compilation
drivers and this explanatory note. Preserve the repository's existing notices
when incorporating the packet.

The semantic dependency is read from the repository's retained
`verification/k215/simplification/proposals/checked-affine-core/affine_core/source_deps/K230/RM.v`
under `k225-formal/`. Its SHA-256 is
`214a6016420e48f4432565ce97f1a27d07ac42642f8ed170d5d0ee02c5994ee8`.
The pilot compiles those exact bytes; it does not define an independently chosen
replacement semantics. The old and new literal DAG source SHA-256 values are,
respectively,
`a12b21cb4e216049ed4bf657c9de1ee1ca467e47f05deccee32cc76a96927445` and
`ba2b28487ae978bd27b0d804e9b2bde6d9adcd1dd575de55572465c050b86aa1`.
