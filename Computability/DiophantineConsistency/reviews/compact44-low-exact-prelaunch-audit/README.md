# Conditional no-build symbolic low-mask population review

This reviews replay driver `7beb48d390`, SHA-256
`ff72d79a6e1a2cec2074f94d5f668048bbe3690e152dc3a86eb3bd78d65edf88`.
The three proposed source modules aim to prove `support.card=985` and that the
symbolic finite-list low mask has population 589083 in IΣ₁ models. The first
module's population lemma retains the cardinality hypothesis; the final
module supplies it from the second. **This prelaunch review compiles no Lean**
and does not establish the theorem. Even a successful pair would not identify
the symbolic list value with retained MC bytes or the equation's graph port,
or prove the high-mask population, machine/checker calibration or PRA claim.

The exact driver's real read-only `verify()` completed successfully in session
78820, rerunning the independently audited concrete-mask ancestry and checking
both same-side seeds. The wrapper pins all three source hashes, the concrete
parent and monitor, copies each source into its respective side, checks
source/object collisions, compiler exits, named axiom reports and allowed
axiom sets, warning/error/`sorryAx` rejection, direct dependency outputs and
paired results, and reruns its parent at the end. The package and dynamic
ancestry remain inherited limitations; checks are point-in-time, not a
continuous integrity guarantee.

The reviewer `audit.py` independently rechecks the exact committed driver,
static source/parent pins and both seeds, and runs a fake six-child loop. The
fake loop substitutes the compiler, dependency query and parent preflight; it
rejects wrong theorem names, injected warnings, `sorryAx`, and altered
dependency output. Separate tests reject a bad source pin, existing output and
optimized Python. These are control-flow tests, not Lean proof evidence. The
reviewer's static script does **not** itself rerun the long concrete-mask
ancestry; its separately observed full driver preflight is recorded above.
The monitor bytes match the earlier independently tested monitor; its
leader-RSS/disk/time checks are sampled, not hard process-tree quotas.
`--deps` and audit subprocesses use ordinary timeouts, not monitored
RSS/descendant-group controls.

A paired build is conditionally ready only with a trusted clean **initial**
loader/interpreter environment and an externally protected stable-HEAD,
sole-Lean window. This driver does not enforce HEAD stability and stripping
child environment variables cannot retroactively protect its initial loader.
An independent post-build audit must check actual outer and all six child
exits, exact theorem names/axiom sets, imports, sources, objects and logs, and
retain the symbolic-value/retained-MC/graph boundary.

Reproduce the static and mock review from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-low-exact-prelaunch-audit/audit.py
```

The static audit exited 0, and separately observed full parent preflight
session 78820 exited 0. See `CHECK.json` and `terminal-observation.json`.
Original `/tmp` provider objects are required; changed or missing pins fail
closed.
