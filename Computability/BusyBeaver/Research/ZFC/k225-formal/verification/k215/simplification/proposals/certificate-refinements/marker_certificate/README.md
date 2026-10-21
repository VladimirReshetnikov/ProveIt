# A checked finite certificate for the two-marker family

This directory replaces separate handwritten proofs for M124 and FM215 by
one generic, verified finite-table certificate. It also supplies M125, the
provider-125 instance already described as an option in the earlier M124
note. **Every table here has 215 working states. No 214-state result is claimed.**

## Checked results

`MarkerFold.v` (322 lines) proves `checked_fold`: when the finite Boolean
certificate is true, the two exact tables have equivalent halting behavior
from state 0, for every integer head position and every complete Boolean tape.
It also proves `timed_simulation`: each old n-step execution has a matching
new m-step execution with n <= m <= 3n, the same whole tape and head, and
the prescribed control identification.

`MarkerInstances.v` (35 lines, generated tables excluded) instantiates the
theorem for M124, FM215, and M125, and gives an explicit proposition-transport
corollary for M125. All three modules compiled under Coq 8.18.0 / OCaml 4.14.1.
Six printed theorem assumption reports are closed under the global context;
recursive `coqchk -silent MarkerInstances` also passed. The receipts and raw
logs are under `verification-final/`. There are no admitted or custom axioms.

The checker verifies all finite rows, equal table lengths, the two incoming
marker conditions, ordinary-row agreement under the state map, the local
three-step shapes, and halt stability. Its correctness theorem also covers
indices outside the finite row range. The construction needs no start-tape
or register invariant: both marker roles are noninitial, and every incoming
old transition writes the required predecessor marker.

## Exact concrete rule

The generic parameters for all three examples are

    a=124, b=127, halt=254, u=62, v=14, w=138, provider0=8.

Only `provider1` varies: 59 for M124, 109 for FM215, 125 for M125. The old
zero branches go from roles 124 and 127 to 62 and 14. Their one branches
both go to 138. Incoming rows write predecessor bits 1 and 0 respectively.
The new table merges the roles at 124 and uses 127 as a selector. On zero
it reads the predecessor and returns through an existing provider, preserving
all tape cells. The roles therefore take one or three new steps per old step.

M125 has the following four replacements relative to K215:

    110 0 0 R 124
    124 0 0 L 127
    127 0 0 R 8
    127 1 1 R 125

The file `M125.dense.tm` is the exact bijective relabeling to working labels
0 through 214 and halt 215. The mapping and both hashes are retained in
`M125.canonicalization.json`. This finite relabeling is audited in Python;
the compiled theorem uses the native table.

## Model and endpoint boundary

The native Coq tables have 303 list slots because some native labels are
sparse. Exactly 215 slots have two outgoing rows. `Halts` means reaching
the designated halt label 254 under a totalized step function that leaves
a configuration fixed on missing rows. The independently audited complete
working rows and transition closure exclude nonhalt holes from every run
starting at 0. Thus this predicate has the conventional TM meaning on these
literal tables. `put_standard` proves agreement with ordinary point updates;
sharing no-op writes avoids needing function extensionality.

These are compiled **table-to-table** theorems. A compiled bridge to the
repository's zipper/dense representation and composition with its complete
ZFC endpoint remain separate integration work. Ordinary composition with
the accepted exact K215 theorem is immediate after the representation
identification, and the elementary finite simulation is formalizable in
ZFC. The generic calibration corollary exposes the inherited calibration
as a theorem premise rather than pretending to prove it here.

## Reproduce

The finite exact-data and complete startup corroboration is:

    python3 verify.py --output /tmp/marker-finite.json

It checks all four literal tables against the generated Coq data, exact
state counts and target closure, the dense renaming, and every matching
boundary through the complete blank startup. For each variant, 95,714 old
steps correspond to 95,840 new steps, with 63 three-step blocks; the common
final configuration has control 84, head -8, and the same 95 one-cells.
This finite run is corroboration; the unbounded conclusion is the theorem.

To compile from fresh sources and run the recursive checker:

    python3 build.py --out /a/fresh/output/directory

The driver serializes compiler use. `generate_tables.py` checks exact literal
regeneration by default; its optional `--output` writes a new generated file.
Sources, tool identity, command status, logs, and object hashes are retained
in each fresh build. Compiled objects are omitted from the delivery.

## Attribution

The family, K215 parent, M124/FM215 concrete tables, marker invariants, and
positive simulation idea are inherited from the inspected ProveIt packets.
The new contribution is the shared finite checker, its generic soundness
proof, its three checked literal instances, and the explicit M125 files.
Provider 125 was already suggested; no priority claim is made for it.
See `NOTICE.md` and the copied licenses for the inherited components.
