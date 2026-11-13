# Independent AQ16 paired-workflow review

The review passed with actual process exit 0 in the recorded
[terminal observation](terminal-observation.json). It compares the fixed
52-module policy with the guarded-author manifest, every recorded author row
and log, and the independently audited AQ16 author receipt. All 127 ordered
report names match; eleven modules are required to produce no reports. The
three terminal reports name the native-refutation and translated-consistency
endpoints. Four policy mutation controls reject missing modules or reports,
extra reports in a silent module, and a changed module order.

The review compares the executable machinery against the independently
reviewed AQ17 workflow at commit `91afc84bd4`: the sibling rebuild, comparison
and coordinator scripts are byte-identical, and the planner, preparer and
freezer differ only in their pinned task policy and endpoint names. This
preserves full historical parent authentication, separate sibling seeds,
protected provider/toolchain roots and actual process-exit gates. The runbook's
shell and five embedded Python blocks parse; it requires the observed and
audited parent pair, independently recorded AQ16 author and workflow audit
exits, and a stable HEAD through preparation.

In a detached temporary copy, all five fixture suites passed, including real
Lean toy siblings and a full parent/freezer/extension chain. All five
optimized-Python negative controls were rejected. The actual detached-suite
exit and detailed fixture outputs are in [receipt.json](receipt.json); source
copies were byte-identical before and after. The separate provisional graph
survey has 1,209 parent dependencies and 52 additions, while the actual
workflow retains and authenticates all 1,210 parent rows.

This is a static policy and synthetic-workflow review, not a real AQ16 paired
replay or a theorem about the PDF. A future real run still requires observed
preparer and coordinator exits and an independent artifact audit. It inherits
the historical parent, package-transitive, dynamic-load, transient-mutation
and unobserved outer Foundation-wrapper-exit limits.

Run with ordinary Python after preserving and moving aside only this packet's
receipt:

```sh
python3 Computability/DiophantineConsistency/reviews/ipra-standard-aq16-independent-workflow-audit/audit.py
```

The checker needs the pinned historical parent manifest, source repository,
Lean toolchain and ordinary fixture dependencies. It does not execute the
real-run procedure and rejects optimized Python.
