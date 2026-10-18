# Exact Rotation244 blank startup

Lean now proves the complete **407,931-step blank run** of the exact
[rotation244 table](candidate-rotation244/zfc_rotation244.tm), including its
state, head and every tape cell. The fast lookup, first checkpoint and ten
continuation modules pass **76 named axiom probes and 111 typed callers**,
with zero warnings.

| Checked layer | Modules | Probes / callers |
| --- | ---: | ---: |
| [All-state fast lookup](../../Lean/BusyBeaver/ZFC/FastTableRotation244.lean) | 1 | 2 / 4 |
| [First 1,024 steps](../../Lean/BusyBeaver/ZFC/BootRotation244First.lean) | 1 | 4 / 7 |
| Continuations through [step 407,931](../../Lean/BusyBeaver/ZFC/BootRotation244Chunk010.lean) | 10 | 70 / 100 |

The final `bootstrap407931` theorem gives
`ZipRep (machineRotation244.run 407931) checkpoint407931`.
`bootstrap_active_through` also rules out halting at any earlier time through
that endpoint. The exact final configuration has canonical state 87 (old
state 96), head −5 and this complete finite zipper:

* Left list: one `true`, followed by nine `false` cells.
* Right list: 181 `false` cells, one header `true`, then the unary register
  encoding of `[0,0,0,3,0,0,3,0,0]` followed by 167 registers of value one.

The right list has 707 cells and no trailing padding. The entire tape has
351 one cells; every exterior cell is zero. The checkpoint therefore retains
all spare registers and the zero exterior needed for a later dispatch-frame
identification.

The [fast-table record](results/fast-table-rotation244-verification.json)
checks equality with `machineRotation244` on every state and input bit.
The [first checkpoint](results/rotation244-bootstrap-first-verification.json)
and [final bootstrap record](results/rotation244-bootstrap-verification.json)
then compose 35 finite kernel calculations through `zipBlock_sound`.
Generated checkpoint data remain untrusted inputs until those calculations
pass. The typed audits include readback at an arbitrary integer tape
position. Each source/audit pair shares a 120-second limit, uses one thread
and 4,096 MiB with default Lean proof limits, and records its fresh object
before auditing. The longest actual pair took 39.75 seconds.

The [ordered unit manifest](rotation244-bootstrap/completed-units.json),
[publication summary](results/rotation244-bootstrap-publication.json) and
[lossless text history](rotation244-bootstrap/history.json) preserve the
actual records, raw logs, source/audit snapshots, original guards, generated
data, pending drafts and author-disclosed reviews. The guards reuse exactly
selected historical source/object providers. Their original scratch paths
remain in provenance, and compiled caches are excluded from the packet;
reproduction is subject to those [recorded cache requirements](rotation244-bootstrap/REPLAY.md).
Publication performs no new proof or simulation run.

For the 243-state goal, this startup supplies the binary checkpoint that
must be identified with the [calibrated rotation source seed](source_rotation244.md).
The [rotation runtime contracts](rotation244_runtime.md) are also checked.
The [exact decoder tree and dispatch-frame identification](rotation244_tree_frame.md)
are now checked as well. Complete decoder-site coverage and final binary
composition remain pending. The existing
[Combined243/Rotation244 equivalence](combined243_simulation.md) can then
transfer the completed rotation endpoint to the exact 243-state machine.
The compensated244 machine remains the smallest closed external Lean
consistency endpoint at this checkpoint. Internal PA formalization remains
open, including transfer of the existing arithmetic results for the earlier
246-state table.

The proof retains the original Mira-Cult program lineage, Jeff Ketchersid's
calibration, Andrew James Wade's register semantics and the preceding
ProveIt routing and loop-rotation work.
