# Prepared resumable static-header traversal — not yet authorized to run

This packet prepares a bounded continuation of the prior 64-module header
inventory; it has **not** launched that continuation. A separate independent
review must inspect the whole implementation and its controls before any launch.
`launch.py` also refuses to start without a `review-gate.json` whose decision is
`PASS_PRELAUNCH_REVIEW`, whose `reviewer` is named, and whose `code_hashes` are
exactly those returned by `launch.code_hashes()`. The gate is a local workflow
control, not cryptographic proof of reviewer independence. No such gate or run
is supplied here. The reviewer should explicitly examine any OS and provider
assumptions; fixing a defect requires a fresh review and a new gate.

This revision addresses the independent v1 review in
`reviews/nine-variable-header-resume-prelaunch-independent/`. The original
packet is also preserved at `research/nine-variable-header-resume-preparation-audited-v1/`.
The direct worker now checks the review gate, an inherited one-use supervisor
pipe, a new session and its parent before loading the inventory. This is an
accidental-bypass guard, not protection against an adversary controlling local
processes or files. Launcher helper hashes are checked against the gate before
loading them; the worker checks the pinned inventory bytes before executing
that helper. These file-hash checks assume no concurrent transient substitution.

## Coverage and authenticated continuation

`test_preflight.py` replays the pinned prior graph from its original 24 seeds:
64 visited modules and the exact 199-node pending order. It adds the complete
128 source-declared external leaves (including `Init`) for the full
nine-variable closure, producing a 287-node initial queue. The two originally
seeded Matrix targets remain useful diagnostics, but reachability is computed
separately from each of the 128 actual seeds; a diagnostic seed alone does not
establish a path from the project. The target set additionally includes
`Mathlib.LinearAlgebra.Matrix.Defs`. A path is reported only when all its
headers have been expanded. Every per-seed closure with any unexpanded name is
marked incomplete; queue exhaustion would establish only the recorded static
header reachability under the stated policy.

The worker replays baseline and checkpoint processing order, records imported
names from each serialized module part, and checks every checkpoint's full
frontier, seen set and unchanged baseline records. It authenticates previous
checkpoints via successful terminal receipts and a hash-linked chain back to
pinned original inputs. It replays every ancestor and checks that each child
extends the parent without rewriting existing modules, artifacts or namespace
observations. It checks source hashes for the 1,212 project sources,
the existing provider-selection policy and root identity, and full hashes for
selected objects and their companions at batch boundaries; namespace markers
are guarded too. These checks are point-in-time checks and do not prevent
transient mutation during a read. They do not inventory all alternate providers
for newly reached modules. The prior 64-node packet separately recorded
alternate-provider guards, but this continuation does not extend that survey.
The declared namespace-selection policy was checked by direct `lean --deps`
for initial seeds only. Selected static headers, dynamic Lean loading, provider
collisions, and successful combined imports are distinct claims. Neither a
missing discovered path in a partial run nor a positive header path by itself
proves a combined import succeeds or fails.

## Bounds and cleanup

A proposed batch handles 1–64 newly visited nodes, with a maximum 60-second
outer timeout, 3.5-GiB owned-session aggregate RSS ceiling, 10-GiB available
memory floor and 4-GiB free disk floor. The Lean reader itself is limited to
2,400 MiB and one thread. Each run uses an exclusive directory and a low
CPU/I/O priority. These are best-effort sampled limits, not kernel-enforced
memory limits: sampling can overshoot. A resource stop is a failure and never
publishes a checkpoint.

The supervisor starts a new session and uses Linux child-subreaper adoption.
On monitor exceptions, timeout/resource stops, or leader exit, it signals and
reaps session descendants, checks for remaining session members, and refuses a
success receipt on cleanup errors. Signal errors are recorded while cleanup
continues for other members; a later successful drain still has a failing
receipt. This assumes the spawned workload does not
escape its session; a deliberately daemonizing descendant could evade session
tracking. SIGKILL of the supervisor or machine failure is outside Python's
cleanup guarantee. The synthetic `test_supervision.py` controls create a
child and grandchild in a separate process group within the session, exercise
monitor exception, leader exit and timeout, and require both `/proc` entries
be absent afterward. They do not establish production behavior for every OS
failure or workload.

A checkpoint is eligible for reuse only when its terminal receipt records a
zero child exit, no monitor failure, complete session drain, unchanged code,
and a matching result hash. No project module is compiled. A future launch
will run a Lean serialized-header reader, so requires the reviewed resource and
provider assumptions to remain valid. Failed batches retain logs, do not publish
a valid checkpoint, and must restart from the last successful parent.

## Controls executed

From this directory, these commands were run successfully with exit 0:

```
python3 -I -S -B test_core.py
python3 -I -S -B test_preflight.py
python3 -I -S -B test_supervision.py
python3 -I -S -B test_worker_gate.py
```

The JSON control outputs are retained alongside their scripts. They are
synthetic queue/gate/process tests and a read-only replay of pinned inputs;
none runs Lean or traverses new headers. Reviewer should inspect the scripts,
not infer broader properties from their passing results. Run results will be
separate and must not be confused with these preparations.
