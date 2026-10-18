# Checked rotation source equivalence and logical calibration

Five Lean units now establish the exact rotated register-program interface,
its equivalence to the routed source for arbitrary register files, and its
logical-seed calibration to native, ZF and ZFC refutation. The five actual
source/audit runs pass **34 named probes and 40 typed callers**, with zero
warnings and only standard Lean axioms.

| Unit | Checked conclusion | Probes / callers |
| --- | --- | --- |
| [ProgramRotation244](../../Lean/BusyBeaver/ZFC/ProgramRotation244.lean) | Exact rows 5/6 overrides, other rows, root 202 and storage bound 203 | 7 / 7 |
| [RMDagLoopRotation](../../Lean/BusyBeaver/ZFC/RMDagLoopRotation.lean) | Both local loops have the same complete register-file normal form | 6 / 8 |
| [RMDagContextSubstitution](../../Lean/BusyBeaver/ZFC/RMDagContextSubstitution.lean) | Equivalent local macros preserve structured runs in an explicitly admitted context | 5 / 6 |
| [SourceRotation244](../../Lean/BusyBeaver/ZFC/SourceRotation244.lean) | Rotated and routed programs halt equivalently from the empty pointer for every register function | 9 / 10 |
| [CalibratedRotation244](../../Lean/BusyBeaver/ZFC/CalibratedRotation244.lean) | At `LogicalSeed246.initial`, rotated-source halting iff native/ZF/ZFC refutation, and nonhalting iff ZF/ZFC consistency | 7 / 9 |

The interface changes row 5 to `(decnz6, cont2)` and row 6 to `(inc0, node5)`.
Its 203 stored nodes describe a register program, not a binary-machine state
count. Both generic loops finish with source zero, destination
`R dst + R src + 1`, and every other register unchanged. The context theorem
retains local equivalence, shared-row, admitted-child and root hypotheses;
its induction includes recursive restart and assumes no global termination.

The concrete source unit discharges those hypotheses for the actual programs.
It checks both finite well-formedness bounds, identifies the structured and
path programs, and uses a context excluding internal nodes 4/5 while replacing
entry 6. Its final theorem quantifies arbitrary register functions. The final
calibration composes this result with the existing routed-program bisimulation
and logical seed; it is a closed external Lean theorem about that register
program from that seed.

Actual records are retained for the
[interface](results/source-rotation244-program-verification.json),
[loop](results/source-rotation244-loop-verification.json),
[context](results/source-rotation244-context-verification.json),
[concrete source](results/source-rotation244-source-verification.json), and
[calibration](results/source-rotation244-calibrated-verification.json).
Proof sources and typed audits are byte-identical to their successful runs.
The [source history](source-rotation244-formal/source/) preserves the concrete
unit's failed first attempt: one `rw` could not see through `ofProgram`.
The only proof repair adds `dsimp only [ofProgram]`; the statement, finite
data and audit remain unchanged. Both preparations, failed raw log, successful
logs, original guard/boundary, repair diffs and original source-only review
are retained. The calibration passed on its first actual attempt. The earlier
three-unit packet and its unexecuted drafting histories remain unchanged.

The project-provider counts are 5, 1, 1, 8 and 198 respectively, all with the
recorded Init/compiler pair. The calibration selects only its actual import
closure from broader historical parent evidence. It does not freshly rebuild
those parents. Each source/audit pair shares 120 seconds, runs serially with
`-j1 -M4096` and default proof limits, captures its fresh object before audit,
and checks inputs and first providers afterwards. There are no version
queries, dependency builds, downloads or distributed caches. Reproduction
requires the exact historical providers named by each boundary, including
scratch paths; these packets do not bootstrap a clean checkout. Installed
guards change only path discovery and source/audit/boundary defaults, with
exact inverse diffs retained.

```sh
python3 -B check_source_rotation244.py --prepare-only --output /tmp/rotation-source-prepared
python3 -B check_source_rotation244.py --output /tmp/rotation-source-actual
python3 -B check_calibrated_rotation244.py --output /tmp/rotation-calibrated-actual
```

The [exact Rotation244 blank startup](rotation244_bootstrap.md) now proves
all 407,931 transitions and the complete final tape. The
[binary runtime contracts](rotation244_runtime.md) are also checked, retaining
coverage and initial-frame hypotheses. Decoder coverage and the checked
dispatch-frame identification must still connect that checkpoint to this
source seed. The checked
[Combined243/Rotation244 binary equivalence](combined243_simulation.md)
remains relative until that connection is supplied. These source and startup
theorems therefore do not yet close a new 243/244 binary consistency endpoint.
Internal PA formalization remains open. The source transformation retains the original
Mira-Cult program lineage, Jeff Ketchersid's calibration and Andrew James
Wade's structured register semantics, together with the preceding ProveIt
source and routing work.
