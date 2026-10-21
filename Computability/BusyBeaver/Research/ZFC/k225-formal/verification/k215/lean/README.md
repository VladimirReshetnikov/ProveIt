# Serial Lean check of the 215-state endpoint

The original fresh Lean check passed: all 204 project modules and both closed-client
audits compiled. The [final record](actual/final-review.json) binds the exact
module and dependency sets, baseline sources, objects, and compiler logs.
The ten audit reports use only `propext`, `Classical.choice`, and `Quot.sound`;
neither audit has warnings. The project sources retain 34 linter warnings.

The [subsequent simplification check](../simplification/phase5/README.md) rebuilds affected
modules against this pinned baseline and reruns both endpoint audits. Its current
closure contains 184 project modules; the audits
still have zero warnings and only the same three allowed axioms. The historical
204-module receipts below are unchanged.

The portable driver rebuilds the exact project import closure of
`BusyBeaver.ZFC.KEndpoint215` from current source, then checks two explicit
closed-client audits. The endpoint uses the dense 215-state machine and relates
blank-tape halting to a finite derivation of falsity from `ZFCax_s`; its companion
theorem relates nonhalting to the absence of such a derivation.

From the repository root, with its pinned Lean toolchain installed:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/lean/build.py \
  --out /tmp/k215-lean-reproduction
```

The output directory must initially be empty. Repeating the same command resumes
only objects whose source, direct dependency objects, compiler identity,
recorded object companions, and original compiler log still match. A different driver or repository cannot
adopt that output directory. Every compilation attempt keeps a source snapshot,
exact command, log, timing, and outcome. Each invocation also preserves its own
source inventory and toolchain queries.

The driver uses a separate Lake workspace and project object directory; it does
not load the repository's cached project objects. The shipped Lean core remains
the compiler trust boundary. The current closure contains 184 project modules
and only the external `Init` boundary. It checks the exact final module set and
direct dependency edges, all source bytes, and all recorded object companions.

Each command compiles one Lean module with one worker and a 12,288 MiB cap. The
default wall limit is 900 seconds per module and 120 seconds per audit. The
shared `/tmp/proveit-k215-proof-build.lock` serializes this driver with the Rocq
build. Timeout or interruption kills and waits for the whole dedicated process
group before releasing that lock. Do not run an independent compiler that
ignores the shared lock while this check is active. Optional resource arguments
are shown by `--help`; changing them does not change the theorem statements.

`EndpointAudit215.lean` has independently authored closed clients for the literal
row count, expanded finite-run halting equivalence, and nonhalting equivalence.
`K215Audit.lean` additionally prints axiom reports for the endpoint, dense
renaming, boot, site coverage, and source correspondence. The driver requires
all ten reports and rejects axioms outside `propext`, `Classical.choice`, and
`Quot.sound`.

The original source certificate was partitioned into a data module, 32 independent
kernel checks, and the public facade. The current forward-only certificate uses
16 checks and the generic symmetry theorem; see the
[second simplification checkpoint](../simplification/phase2/README.md). That original partition retained every declaration statement and proof body. Further repairs use one typed congruence lemma and
local irreducibility for the dominated-axiom certificate, and narrow namespace
openings in the dispatch and seed proofs. The endpoint statements, machine,
certificate nodes, and semantic assumptions are unchanged. All four failed
attempts remain in the [execution history](actual/attempts.json): the original
monolithic 900-second timeout and three elaboration failures. Their partial
outputs and axiom reports are excluded from the final closure.

This portable wrapper is distinct from the historical execution wrappers.
Its exact inventory was compared with the partitioned 204-module build, and its
normal, timeout, and interruption paths were tested using noncompiler child
processes. Those controls do not constitute a second full Lean replay. The
completed actual build used the preserved historical serial runners and their
safe successors. The [publication map](publication-complete.json) locates their
logs, source repairs, and the two [independent](actual/audit/independent/compiler.log)
and [component](actual/audit/axiom-components/compiler.log) audit outputs.

The [independent driver review](../independent-audit/portable-lean-v2/review.json),
[noncompiler controls](controls/result.json), and
[preserved history](history/README.md) give the execution and repair boundaries.
