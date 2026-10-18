# Routing245 symbolic execution and runtime

Five Lean modules prove that accepted instruction certificates describe actual
execution of the literal 245-state machine, then compose those instruction
segments into halting equivalence. The runtime theorem still requires complete
site coverage and a related initial configuration. The
[complete startup proof](routing245_bootstrap.md) now supplies the actual
blank-run frame. The [complete coverage proof](routing245_coverage.md) and
[final composition](routing245_binary.md) now discharge these premises for
the literal blank-start machine.

`RuntimeInstanceRouting245.register_halts_iff_binary` states, for any register
program `p`, logical configuration `logical` and binary configuration `binary`,

```lean
Covered p → Related p logical binary →
  (RegisterPath.Halts p logical ↔ BinaryHalts machineRouting245 binary)
```

The `allSites_halts_iff_binary` client obtains `Covered p` from an exact tree
identity and successful `SiteCoverage.allSites` check. Neither theorem assumes
a bound on register values or total runtime. The accepted-site and initial-frame
premises remain explicit in this reusable runtime theorem; the closed
blank-tape endpoint supplies both proofs.

| Layer | Checked contract | Probes / callers | Source / audit seconds |
| --- | --- | ---: | ---: |
| [SymbolicRouting245](../../Lean/BusyBeaver/ZFC/SymbolicRouting245.lean) | Accepted symbolic traces give real positive machine segments, including the final halt action. | 15 / 15 | 5.427 / 0.469 |
| [SiteRouting245](../../Lean/BusyBeaver/ZFC/SiteRouting245.lean) | Accepted sites implement their instruction and both decrement guards. | 12 / 13 | 0.868 / 0.474 |
| [Routing245Simulation](../../Lean/BusyBeaver/ZFC/Routing245Simulation.lean) | Exact conversion between symbolic representations and complete dispatch frames. | 14 / 15 | 0.973 / 0.530 |
| [InstructionRouting245](../../Lean/BusyBeaver/ZFC/InstructionRouting245.lean) | Positive instruction segments preserve the dispatch frame and nonempty spare suffix. | 7 / 7 | 0.743 / 0.449 |
| [RuntimeInstanceRouting245](../../Lean/BusyBeaver/ZFC/RuntimeInstanceRouting245.lean) | Both halting directions under coverage and initial-relation premises. | 11 / 12 | 0.654 / 0.482 |

All **59 named theorem probes and 62 typed callers** pass, with zero warnings
in the selected runs. The axiom reports use only `propext` and `Quot.sound`,
or no axioms. The guards select respectively 12, 17, 21, 22 and 26 project
providers plus Init and Omega. Each source/audit pair shares a 120-second
budget, one thread and 4,096 MiB, with default proof limits for the new files.
Existing imported objects are explicit checked boundaries; no dependency
rebuild or compiler-version query occurred.

The new `DispatchFrame64` requires
`64 ≤ logical.path.length + gap` and preserves the entire infinite tape,
including its zero exterior. Register values, additional gap, finite padding
and the nonempty finite spare suffix are arbitrary. Increment appends one
value-one spare; positive decrement preserves the suffix and adds one gap
cell. The frame proof accounts for consumed paths and implicit zero bits.
The historical 40-cell frame definition remains unchanged.

Literal symbolic steps use the checked fast table for this exact machine;
the proof does not transport all rows by a state renaming. The checker fuel
of 4,000 bounds certificate computation, not the concrete register values or
total binary execution. Actual positive segment lengths support the generic
runtime simulation theorem, including its reverse halting implication.

The selected raw records are
[Symbolic](results/routing245-symbolic-verification.json),
[Site](results/routing245-site-verification.json),
[Frame](results/routing245-frame-verification.json),
[Instruction](results/routing245-instruction-verification.json) and
[Runtime](results/routing245-runtime-verification.json).
The [publication manifest](routing245-execution/publication.json) and
[history](routing245-execution/history.json) retain exact sources, audits,
guards, preparation records, execution logs and reviews. Frame run1 already
passed, with one unused-simplification warning; the selected run2 removes
only that unused `List.append_assoc` argument. Both attempts are preserved.
Recorded scratch paths and object hashes describe the actual runs. Compiled
caches are not included, and publication performs no proof replay.

The [source-program bisimulation](bisim_routing245.md) and
[local register operations](routing245_local.md) are already checked.
The [407,915-step blank initialization](routing245_bootstrap.md) is now
checked, including its complete runtime frame. Acceptance of all 8,391
guarded cases is proved by [complete coverage](routing245_coverage.md), and
the [closed binary endpoint](routing245_binary.md) composes these results.
PA internalization remains open. Attribution follows the
[candidate notice](candidate-routing245/README.md): Mira-Cult's calculus and
machine, Jeff Ketchersid's verification, Andrew James Wade's compiler framework,
and the subsequent ProveIt reductions and formalization.
