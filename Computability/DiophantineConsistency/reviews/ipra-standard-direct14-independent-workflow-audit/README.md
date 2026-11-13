# Independent direct-square 14-variable paired-workflow review

The review passed with actual process exit 0 in the recorded
[terminal observation](terminal-observation.json). It compares the fixed
five-module policy with the guarded-author manifest, every recorded author row
and log, and the independently audited author receipt. All eight ordered
report names match; four modules are required to produce no reports. Four
policy mutation controls reject missing modules or reports, an extra report in
a silent module, and a changed module order.

The initial [review attempt](attempt-1-observation.json) found that the launch
runbook expected 11 author direct-import edges while the actual audited run
has 16; its exact [review script](attempt-1-script.py) is retained. Commit
`dbe2ba1fcb` corrected the gate. The successful review parses and executes
that exact runbook gate against the audited author receipt: 16 is accepted and
11, 15 and 17 are rejected. It also reruns the workflow author's gate test,
including its optimized-Python rejection.

The review compares the executable machinery against the independently
reviewed AQ16 workflow at commit `cb8ceed959`: the sibling rebuild, comparison
and coordinator scripts are byte-identical, and the planner, preparer and
freezer differ only in their pinned task policy and endpoint names. This
preserves full historical parent authentication, separate sibling seeds,
protected provider/toolchain roots and actual process-exit gates. The runbook's
shell and five embedded Python blocks parse; it requires the observed and
audited parent pair, independently recorded author and workflow audit exits,
and a stable HEAD through preparation.

In a detached temporary copy, all five fixture suites passed, including real
Lean toy siblings and a full parent/freezer/extension chain. All five
optimized-Python negative controls were rejected. The detached-suite exit and
fixture outputs are in [receipt.json](receipt.json); copied inputs matched
before and after. The provisional graph survey has 1,099 parent dependencies
and five additions, while the real workflow retains and authenticates all
1,210 parent rows.

This is a static policy, real-receipt gate and synthetic-workflow review, not
a real direct14 paired replay or a theorem about a PDF. A future real run
requires observed preparer and coordinator exits and an independent artifact
audit. It inherits historical parent, package-transitive, dynamic-load,
transient-mutation and unobserved outer Foundation-wrapper-exit limits.

Run with ordinary Python after preserving and moving aside only this packet's
receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/ipra-standard-direct14-independent-workflow-audit/audit.py
```

The checker needs the pinned parent manifest, source repository, real audited
author receipt, Lean toolchain and fixture dependencies. It does not execute
the real-run procedure and rejects optimized Python.
