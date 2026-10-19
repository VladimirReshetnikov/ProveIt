# Checked runtime contracts for the exact 240-state machine

Nine freshly checked Lean units prove the 240-state machine's general runtime
contracts for arbitrary register values and complete tape configurations.
They pass **106 named theorem probes and 94 typed callers**, with zero warnings.

| Unit | Checked interface | Probes / callers |
| --- | --- | ---: |
| `Rotation240KernelRows` | Nineteen exact transition rows and dispatcher 84 | 20 / 3 |
| `Rotation240Pulse` | Both neighboring-bit cases with arbitrary surrounding tape | 3 / 4 |
| `RegisterMarkRotation240` | Register selection and marking | 10 / 6 |
| `Rotation240Boxes` | Increment and both decrement cases, including the entire register file | 14 / 19 |
| `SymbolicRotation240` | Sound symbolic execution and complete-tape matching | 15 / 15 |
| `SiteRotation240` | Soundness of each accepted instruction-site check | 12 / 13 |
| `Rotation240Simulation` | Register/tape frame conversion at distance at least 64 | 14 / 15 |
| `InstructionRotation240` | Positive binary segments implement accepted logical instructions | 7 / 7 |
| `RuntimeInstanceRotation240` | Halting equivalence under coverage and initial-frame hypotheses | 11 / 12 |

The final
[`register_halts_iff_binary`](../../Lean/BusyBeaver/ZFC/RuntimeInstanceRotation240.lean)
quantifies over a register program, logical configuration and binary
configuration. `Covered` requires every decoder input to reach an instruction
whose site check succeeds. `Related` retains a clean logical path, a nonempty
spare-register suffix and the complete dispatch tape frame. Positive execution
lengths establish both halting directions. The contracts preserve all nine
primary registers, the spare suffix and exterior tape; increment appends a
spare of value one.

These proofs use the [exact 240-state table and fast lookup](rotation240_foundations.md).
All nine canonical selector numbers are recomputed for this table. Old state
255 remains active at canonical state 239. The earlier 244-state proofs
supply proof patterns and unchanged generic lemmas; each concrete 240-state
unit was checked anew.

The [publication record](results/rotation240-runtime-publication.json) lists
all nine actual source/audit runs. The [final runtime result](results/rotation240-runtime-verification.json)
retains the conditional theorem's audit. Sources and audits are byte-identical
to their successful runs, including comments describing their status when
emitted. Every pair used default proof limits, one thread, 4,096 MiB and a
shared 120-second deadline. The selected project-provider counts are
2, 5, 7, 9, 13, 18, 22, 23 and 27. Fresh source objects were recorded before
their audits; input and provider identities were checked afterward.

[Original guards and execution records](rotation240-runtime/provenance/)
and [lossless text history](rotation240-runtime/history.json.gz) preserve the
emission, independent source/guard reviews, preparations and actual logs.
The original guards retain historical scratch and provider paths. Compiled
caches are excluded; a clean-checkout build is not supplied by this packet.
Publication did not run another proof or simulation.

The [source-program halting equivalence](source_rotation240.md) is already
checked. To obtain the closed binary consistency theorem, the concrete
6,455-leaf decoder must still pass all 8,386 guards, and the exact blank
initialization must establish the required `Related` configuration. The
internal PA proof also remains open. Compensated244 remains the smallest
closed external Lean consistency endpoint at this checkpoint.

Attribution follows Mira-Cult's original machine and calculus, Jeff
Ketchersid's verification and calibration, Andrew James Wade's register
semantics, the preceding ProveIt reductions, and the source80 construction.
