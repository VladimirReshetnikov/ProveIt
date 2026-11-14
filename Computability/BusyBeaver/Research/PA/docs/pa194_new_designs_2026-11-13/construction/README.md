# PA194C: a cached-head PA consistency machine

`candidate/pa194C.tm` is the complete binary one-tape machine. It has 194
working states (0 through 193), initial state 0, and separate halt label 194.
The initial tape is all zero, the head starts at cell zero, and every
transition writes, moves one cell left or right, and changes control.
Each row has the form `state read write L-or-R next`. There are 388 rows.

The machine composes the supplied primary PA194 axiom decoder (67 readers,
seven contextual folds) with the supplied PA195C cached-head controller.
Successful modus ponens returns its result in the cache, and Shift tests
that cache alone. Its source therefore has 3,649 primitive instruction
sites instead of the primary PA194's 3,673. It is a different proof-search
controller, not a state renaming or a tape reflection.

The dense table SHA-256 is:

```
d759313c03b515293fe06b12769fa1771d3829a2bad89febaa9b4391990f3a4b
```

The native table SHA-256 is:

```
b35d80b01ce9c2e95c8b29222881f40928247cdeffac322e4643f4f6694cd33c
```

## Reproduce

Use Python 3.10 or later with its standard library, without `-O`:

```sh
python3 build_cached.py
python3 verification/check_cached.py
```

The first command rebuilds the entire table, reproduces the pinned 195C
parent exactly, proves source-map identity by finite comparison, checks all
seven simultaneous folds, replays 4,749 symbolic source contracts, and
checks the full 57,922-step blank initialization. It writes tables and
receipts under `candidate/`.

The second command imports no compiler or arithmetic-box oracle. It
rederives four list-sweep lemmas from the literal table, resolves the source
graph in two independent ways, checks all 4,749 arbitrary-register outcomes,
checks exact dense/native conjugacy, and compares the entire blank seed
tape using a separate bytearray simulator. It writes fresh results under
`verification/results/`. The recorded run took 1,096,302 symbolic steps;
each instruction contract has positive physical duration. Register scope
is all nine independent natural values, with both decrement outcomes and
an arbitrary finite nonempty spare list.

## Mathematics and attribution

`proof_cached.tex` is a report fragment tailored to this machine. It proves
the new finite-trace preservation statement with the pinned 195C machine,
explains the changed command calculus and its all-store proof compiler,
and makes the inherited PA logical calibration explicit.

The conclusion is an ordinary mathematical PA-provability claim, inheriting
the supplied separate-head calculus's syntactic PA calibration. This package
does not claim a new end-to-end kernel-checked Lean or Rocq theorem. The
repository's conditional iPRA endpoints remain conditional.

`logical_reference/` preserves the exact inherited calibration and command
manuscripts. `inputs/` contains pinned parents, grammar, folds and source
maps. `reference/`, `compiler.py`, `symbolic_runtime.py`, and the helper
functions in `baseline_tools.py` are adapted or retained from the primary
PA194 packet. The independent symbolic engine is credited separately in
`verification/reference/README.md` and retains its original license files.
`PROVENANCE.json` records the repository revision and input archives.
