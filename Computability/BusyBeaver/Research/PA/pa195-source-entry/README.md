# PA195 entry source-tree and physical binding

The generator combines the pinned upstream `PA196/Program.lean` with the
original PA195 packet's pinned 69-rule AX grammar: it replaces exactly the
upstream `x67` definition with the grammar root and retains the surrounding
source program. It verifies the upstream file against both its hash and the
archive copy, checks the grammar hash and rule structure, and emits a Lean
source tree. The grammar-to-Lean translation is a small Python generator and
is an explicit remaining source-generation trust boundary.

`PA195SourceEntry.lean` uses the upstream Lean source-tree semantics to check
that site 25 is path `100000`, decrementing logical register 8, and that its
zero and positive successors are sites 27 and 26. It checks both successor
paths, and `entry_binding` combines these exact source facts with the two
already kernel-checked positive physical executions on the actual unfolded
parent table, for every gap and valid complete register file.

Run the fully fresh check from the repository root:

```sh
Computability/BusyBeaver/Research/PA/pa195-source-entry/check.sh
```

The script builds all dependencies in a private `/dev/shm` directory and
pins the imported M6 and source-semantics files. The source-entry theorem has
also been checked against previously rebuilt private Lean dependencies. Its
scope is the single source entry and its two branches. It does not establish
all 3,700 source instructions, an internal PRA/iPRA simulation, or a
consistency equivalence.
