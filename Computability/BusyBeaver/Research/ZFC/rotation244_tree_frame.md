# Checked Rotation244 source tree and startup frame

Two Lean units connect the rotated source's exact tree to its program and the
407,931-step binary startup to the calibrated initial register frame. Their
actual source/audit runs pass **16 named probes and 19 typed callers**, with
zero warnings and only standard Lean axioms.

| Unit | Checked conclusion | Probes / callers |
| --- | --- | --- |
| [TreeRotation244](../../Lean/BusyBeaver/ZFC/TreeRotation244.lean) | The actual rotated program unfolds to the literal tree for every fuel at least 51; exact arbitrary-pointer lookup and complete register-step semantics | 8 / 10 |
| [BootstrapFrameRotation244](../../Lean/BusyBeaver/ZFC/BootstrapFrameRotation244.lean) | The actual blank run at step 407,931 satisfies the runtime dispatch frame for `LogicalSeed246.initial` | 8 / 9 |

The tree retains the 203 stored DAG rows while recomputing every height after
rows 5 and 6 change. Row 4 becomes unreachable. Its complete unfolding has
6,459 leaves, 6,458 internal nodes, depth 51 and exactly one halt. Every generated
row equality and sufficient-fuel unfolding is checked by Lean. The audit also
checks the new increment and continue paths inside subtree `011`. The generator's
comparison with all retained logical sites is additional evidence; the Lean
theorem identifies the tree with `ProgramRotation244.program` itself.

The startup adapter uses the [complete blank prefix](rotation244_bootstrap.md)
and the checked runtime frame. It identifies the entire finite zipper at state
87 and head position −5, including left padding 9, right padding 0, 707 right
bits and 351 one cells. The logical seed has physical register values
`[0, 0, 0, 3, 0, 0, 3, 0, 0]`, distance 181 and 167 nonempty spare registers of
value one. Both tape exteriors are zero. This establishes the actual
`DispatchFrame64` premise without replacing the tape by a finite observation.

The [tree record](results/tree-rotation244-verification.json) and
[frame record](results/rotation244-bootstrap-frame-verification.json) retain
actual source/audit output. The [publication record](results/rotation244-tree-frame-publication.json)
and [lossless text history](rotation244-tree-frame/history.json) preserve the
sources, typed audits, metadata, original guards, preparations, root-generated
literal data, draft frame inventory and disclosed author reviews. The independent
tree review is a source/emitter review; it does not claim another compilation.
Historical pending labels remain in their original source-only records.

Each source/audit pair used a shared 120-second limit, one thread, 4,096 MiB and
default proof limits. The tree reused six imported project providers and Init;
the frame selected 125 imported providers plus Init/Omega from three actual
parents. The BinaryPrefix246 record is an evidence carrier for LogicalSeed246;
its binary endpoint module is excluded from the frame's imports. Fresh objects
were captured before audit and all selected inputs/providers checked afterwards.
The [original guards and reproduction limits](rotation244-tree-frame/REPLAY.md)
retain their historical scratch paths. This publication contains no compiled
objects and does not claim a clean-checkout rebuild of cached dependencies.

Complete decoder-site coverage and the final binary composition remain separate
obligations. Once those are supplied, the checked
[Combined243/Rotation244 equivalence](combined243_simulation.md) transfers the
rotation endpoint to the 243-state machine. These two units do not by themselves
close that binary consistency endpoint or the internal PA proof. The original
Mira-Cult program, Jeff Ketchersid calibration, Andrew James Wade register
semantics, and prior ProveIt routing and rotation contributions retain their
attribution.
