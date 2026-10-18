# Checked Rotation244 runtime contracts

Nine freshly checked Lean units prove the rotated machine's runtime contracts
for arbitrary register values and complete tape configurations. Their source
and audit runs pass **106 named theorem probes and 94 typed callers**, with
zero warnings and only standard Lean axioms.

| Unit | Checked interface | Probes / callers |
| --- | --- | ---: |
| `Rotation244KernelRows` | Nineteen exact transition rows and dispatch state 87 | 20 / 3 |
| `Rotation244Pulse` | Both neighboring-bit cases, with arbitrary surrounding tape | 3 / 4 |
| `RegisterMarkRotation244` | Register selection and marking | 10 / 6 |
| `Rotation244Boxes` | Increment, zero and positive decrement, full register-file effects | 14 / 19 |
| `SymbolicRotation244` | Soundness of symbolic execution and complete-tape matching | 15 / 15 |
| `SiteRotation244` | Soundness of an accepted instruction-site check | 12 / 13 |
| `Rotation244Simulation` | Register/tape frame conversion with distance at least 64 | 14 / 15 |
| `InstructionRotation244` | Positive binary segments implement checked logical instructions | 7 / 7 |
| `RuntimeInstanceRotation244` | Register halting iff binary halting, assuming coverage and a related initial configuration | 11 / 12 |

The final
[`register_halts_iff_binary`](../../Lean/BusyBeaver/ZFC/RuntimeInstanceRotation244.lean)
quantifies over a register program, logical configuration and binary
configuration. Its `Covered` hypothesis requires every decoder input to reach
an instruction whose site check succeeds. Its `Related` hypothesis retains a
clean logical path, a nonempty spare-register suffix and the entire dispatch
tape frame. Positive execution lengths support both halting directions.
The register permutation, all nine primary values, spare suffix and exterior
tape are preserved by the contracts. Increment appends a spare of value one.

The ports use the exact Rotation244 table and its checked fast lookup. Old
state 255 remains an active state, now numbered 243; the changed selector
numbers and dispatch state are freshly checked. No routed-machine coverage
proof is treated as coverage for the rotated machine.

The [publication record](results/rotation244-runtime-publication.json) lists
all nine successful runs; the [final actual record](results/rotation244-runtime-verification.json)
contains the conditional runtime theorem's audit. Sources and audits are
byte-identical to their successful runs, retaining their emission-time
comments. Each pair used one thread, 4,096 MiB and a shared 120-second budget
with default proof limits. The exact project-provider counts were
2, 5, 7, 9, 13, 18, 22, 23 and 27. Every fresh object was recorded before
its audit, and inputs and provider identities were checked afterwards.

[Original guards and the serial execution plan](rotation244-runtime/provenance/)
and [lossless text history](rotation244-runtime/history.json) preserve source
generation, its initial documentation-check failure and corrected emitter,
preparations, actual records and raw logs. Original guards retain historical
scratch/provider paths. Compiled caches are excluded; this packet does not
provide a clean-checkout build. The publication step ran no additional proof
or simulation.

The [407,931-step blank startup](rotation244_bootstrap.md) and
[source consistency calibration](source_rotation244.md) are already checked.
The exact rotated decoder tree, all 8,390 site guard cases and the checked
identification of that startup with the logical frame remain to be supplied.
They will discharge the conditional runtime theorem before the checked
[Combined243 equivalence](combined243_simulation.md) transfers the result to
243 states. The compensated244 machine remains the smallest closed external
Lean consistency endpoint. Internal PA formalization remains separate.

Attribution follows the imported Mira-Cult machine, Jeff Ketchersid's
verification/calibration, Andrew James Wade's register semantics, and the
preceding ProveIt routing and loop-rotation work.
