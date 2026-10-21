# K215 source and certificate representation audit

This packet accompanies the source-equivalence and Rocq checker packets.
`audit.md` distinguishes completed upstream work, checked new artifacts,
and the proposed canonical-graph follow-up.

## Reproduce exact source transformations

From this directory, with Python 3:

```sh
python3 compact_source_trees.py inputs/KSource215Data.lean generated-trees
```

The generator independently reparses every generated shared definition,
unfolds aliases, and compares both complete abstract syntax trees. The output
must match `prototype/KSource215Data.lean` exactly.

For Rocq, supply the original `Cert215Offsets.v` at the commit and SHA-256 in
`provenance.json` (also included in the companion Rocq packet):

```sh
python3 compact_rocq_paths.py /path/to/original/Cert215Offsets.v generated-rocq
```

The generator decodes all 4,480 numeric path codes and compares all 2,240
complete entries, including successors and zero offsets. The companion Rocq
packet includes the generated output, exact certificate equality, generic
mirror theorem, compiler logs, and recursive checker receipts.

## Reproduce the standalone Lean identity

Use the shipped core of Lean 4.32.0; no Mathlib or Lake is needed:

```sh
cd prototype
/path/to/lean-4.32.0/bin/lean SharedTreeIdentity.lean
```

Both `K215TreeSharingAudit.t215_exact` and `tD_exact` compile by `rfl`
and print no axioms. Their abstract tree type is local to this standalone
representation check. The separate `plain_source` packet checks the actual
repository program bindings and semantic source equivalence.

`receipts/SharedTreeIdentity.json` binds the checked source, command, object
hash and raw log. Compiled objects and toolchains are excluded. Generator JSON
files record their own Python-only scope; they do not silently claim a kernel
check. The kernel receipt is separate. This packet does not assert a fresh
complete K215 binary endpoint replay.
