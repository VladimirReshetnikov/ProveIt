# Checked source-level foundations for the loop rotation

Three Lean units establish the two-row rotated program interface and reusable
structured-semantic rules for proving its equivalence to routed245. All three
actual source/audit runs pass: **18 named probes and 21 typed callers**, with
zero warnings and only standard Lean axioms.

| Unit | Checked conclusion | Probes / callers |
| --- | --- | --- |
| [ProgramRotation244](../../Lean/BusyBeaver/ZFC/ProgramRotation244.lean) | Rows5/6 are the exact override; other rows, root202 and storage bound203 are retained | 7 / 7 |
| [RMDagLoopRotation](../../Lean/BusyBeaver/ZFC/RMDagLoopRotation.lean) | Original and rotated local loops have identical complete register-file normal forms | 6 / 8 |
| [RMDagContextSubstitution](../../Lean/BusyBeaver/ZFC/RMDagContextSubstitution.lean) | An equivalent macro can be substituted in an explicitly admitted structured context | 5 / 6 |

The interface changes row5 to `(decnz6, cont2)` and row6 to `(inc0, node5)`.
Its 203 stored nodes are a register-program representation, not a binary-machine
state count. The generic loop theorem assumes only its local row equations
and distinct source/destination registers. For every register function `R`,
both layouts finish normally with source zero, destination
`R dst + R src + 1`, and every other register unchanged. Determinism gives
identical exit/output judgments at their local entries.

The context theorem retains explicit hypotheses: local macro equivalence,
identical rows away from that entry, admitted children, equal roots and an
admitted root. Its proof follows the complete structured `Run` derivation,
including the recursive restart premise. It does not assume termination of
all programs or infer it from acyclic storage indices.

Exact actual records are retained for the
[interface](results/source-rotation244-program-verification.json),
[loop](results/source-rotation244-loop-verification.json), and
[context](results/source-rotation244-context-verification.json).
Sources and typed audits are byte-identical to those runs. Prepared records,
raw logs, source snapshots, source/guard reviews with their authorship roles,
and unexecuted drafting histories are in
[source-rotation244-formal](source-rotation244-formal/).
No actual proof attempt failed in these three units. An earlier metadata-only
parser correction preserved JSON null for the halt operand; its history is
retained separately from compiler evidence. Static candidate WF arrays are
retained as input provenance and are not promoted to checked WF theorems.

The interface guard selects five existing project providers; the two generic
guards each select only RMDag. All use the recorded Init provider and compiler.
Each source/audit pair shares120 seconds, runs serially with `-j1 -M4096`,
and keeps default proof limits. Fresh objects are captured before auditing;
selected inputs and first providers are checked afterwards. There is no
compiler-version query, dependency build, download or distributed cache.
Reproduction requires the exact historical providers named in each boundary,
including scratch paths; this packet does not bootstrap a clean checkout.
Only path discovery and source/audit/boundary defaults change in the installed
guards, with exact inverse diffs retained.

```sh
python3 -B check_program_rotation244.py --prepare-only --output /tmp/rotation-program-prepared
python3 -B check_program_rotation244.py --output /tmp/rotation-program-actual
python3 -B check_rmdag_loop_rotation.py --output /tmp/rotation-loop-actual
python3 -B check_rmdag_context_substitution.py --output /tmp/rotation-context-actual
```

The concrete safe-context and WF obligations, structured/path-semantics bridge,
and calibrated Rotation244 runtime/bootstrap remain separate. These three
units alone do not establish whole-program source equivalence or a new
ZF-consistency endpoint. The checked
[Combined243/Rotation244 machine equivalence](combined243_simulation.md)
is also relative. Internal PA formalization remains open.
