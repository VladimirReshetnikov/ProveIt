# Conditional no-build review of finite table pair

This reviews the exact replay driver `d1b4a61bb4`, SHA-256
`f2d574483b92a6648462a2700a23e2884ea5572c8f5b2162ccf6b068c9d61510`.
No Lean compilation is performed by this review. A successful future replay
would concern the finite table equality and explicit color/index permutation
facts. It would not by itself prove matching-neighbor existence in arbitrary
model tilings, calibrate compact44, or establish an iPRA endpoint.

The actual full driver `--preflight` session 35056 exited 0 at HEAD
`d1b4a61bb4d2e37620855f929fb451ca0aa485ec`, printing manifest SHA
`7f78a6ee9c9f1e3a3e859e0be035ed31c5c3efc29f7c4fcd887881b4a043f0a0`.
It reran the independently audited 342-module endpoint parent, 943-table and
external relabel audits. The accompanying reviewer `audit.py` separately
rechecks the exact driver, all 58 manifest source hashes and committed source
anchors, import order and parent-object availability, array/inverse checker
results, and mocked controls; it does **not** rerun that full parent
preflight. A fresh real build must rerun the driver's own checks at its new
protected HEAD.

The independent fake-compiler loop uses the actual committed wrapper but
substitutes mock preflight, compiler and dependency queries. Its actual run
exited 0 after exercising all 116 planned side/module steps, with separate
controls rejecting wrong axiom sets, injected warnings and wrong dependency
output. The independent guard test rejects wrong HEAD, source pin and
companion bytes, unexpected companions, optimization and missing isolation.
These are control-flow tests, not Lean proof or build evidence. The driver's
actual output checks exact source `#print axioms` names and prescribed sets;
this is not a complete axiom inventory for every inherited declaration.

The wrapper checks full HEAD and tracked-worktree cleanliness at specified
points, pins and copies the source tree, compares each direct `--deps` output
to same-side objects, and guards direct-import companion realpaths/hashes and
corresponding sibling outputs. These are point-in-time checks, not a lock on
files between checks. A build must start with a trusted clean **initial**
native-loader environment and use an externally protected stable-HEAD,
sole-Lean window. The wrapper checks HEAD but cannot retroactively protect the
initial interpreter from inherited loader settings. Its sampled compiler
monitor is not a hard process-tree quota; `lean --deps` and audit subprocesses
have timeouts without sampled RSS or descendant-group enforcement. Complete
package-transitive and dynamic ancestry remains unauthenticated. A post-build
review must inspect the actual outer exit and all 116 source/object/log/import
chains and exact axiom reports.

Reproduce the static and mock reviewer checks from the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/compact44-relabel-pair-prelaunch-audit/audit.py
```

Actual reviewer session 22829 exited 0, without Lean. The earlier full driver
preflight used the recorded HEAD; the driver's `--expected-head` must use the
current full protected HEAD for a new run. Both checks read original `/tmp`
provider artifacts, and missing or changed inputs fail closed.
