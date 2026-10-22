# Serial Lean check of the 215-state endpoint

The original fresh Lean check passed: all 204 project modules and both closed-client
audits compiled. The [final record](actual/final-review.json) binds the exact
module and dependency sets, baseline sources, objects, and compiler logs.
The ten audit reports use only `propext`, `Classical.choice`, and `Quot.sound`;
neither audit has warnings. The project sources retain 34 linter warnings.

The [phase19 check](../simplification/phase19/README.md) passes for 226 providers
(211 project modules and fifteen typed clients): 16 fresh and 210 exact-source
reuses, plus two fresh endpoint audits. All retained profiles match exactly. The
forwarding proofs infer repeated conclusions, and five root interfaces share the
existing iteration theorem. The two unused projection wrappers in each root are
retired after a caller census. The initial old-source baseline stopped on two
inherited `L2Control219` warnings; its failure and the successful successor remain
separate. Every typed client and both endpoint audits have zero warnings.

The [phase18 combined check](../simplification/phase18/README.md) passes for
214 providers (199 project modules and fifteen typed clients): 107 fresh and
107 exact-source reuses, plus two fresh endpoint audits. All nine 215 site batches
were checked fresh. The fourteen earlier client sources and all retained profiles
are exact; the new macro client matches its ten-report baseline. Independent
result review and evidence capture pass. Accepted provider records contain 16 warning occurrences (9 fresh); the fresh warning headlines already appeared in the same modules. All fifteen typed clients and both endpoint audits have zero warnings.

The shared `L2K.AS` type supports the checked record syntax and run contracts.
The old nominal identity and generated qualified namespace are retired; optional
`L2K.AS.mk` / `L2K.AS.np` probes fail and their partial output is excluded.
The [phase18 record](../simplification/phase18/README.md) preserves that failure
and the runtime interruptions. [Phase17](../simplification/phase17/README.md)
and earlier receipts retain their historical scopes.

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
the compiler trust boundary. The current source selection contains 178 project
modules and only the external `Init` boundary.
It checks the exact final module set and
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
16 checks and the generic symmetry theorem. The
[second simplification checkpoint](../simplification/phase2/README.md) records that reduction;
[phase six](../simplification/phase6/README.md) checks 1,426 normalized entries using
512 decoding steps and separates the stable program/tree from certificate data.
The original partition retained every declaration statement and proof body.
The original elaboration repairs used one typed congruence lemma and local
irreducibility for dominated implication, and narrow namespace openings in the
dispatch and seed proofs. Those repairs left the endpoint statements, machine,
certificate nodes and semantic assumptions unchanged; later certificate reductions
are recorded in their respective simplification checkpoints. All four failed
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
