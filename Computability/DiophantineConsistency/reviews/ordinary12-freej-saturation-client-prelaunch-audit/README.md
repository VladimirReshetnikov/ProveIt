# Conditional no-build saturation replay review

This reviews driver `37d04291e8`, SHA-256
`05e5563e0eaf17f7beb6a6e0b5412159b488c12fa615806d85b8678cef917d3f`.
No Lean build is performed by this review. The intended theorem is conditional
on the free-J graph zero and positivity/port bounds, `p₀≥46`, the radix and
repunit identities, a port split, mask bounds and residues, the stated
population identity and positivity condition. See the source-closure review
`172e4b4cb1` for those explicit hypotheses. The driver does not prove these
hypotheses for the retained compact44 ports or establish an iPRA endpoint.

The real read-only `verify()` preflight passed in session 59562 against the
independently audited graph-population parent and the point-in-time four-source
closure, with 109 inherited objects per side. The wrapper pins the source
scan, parent evidence and warning policy; freezes four sources and the client;
reads the client's imports from its frozen copy; rejects missing same-side
project imports, unexpected direct dependencies, errors, `sorryAx`, wrong
axiom names or disallowed axiom sets; and compares the paired outputs. The
actual final reviewer audit session 6098 also reran this preflight and exited 0.
Provider and source hashes are checks at points in time, not continuous
integrity or complete package-transitive/dynamic ancestry guarantees.

The proposed warning policy accepts **only** the full observed ordered text
of four `ArithmeticBinaryCarry` linter warnings at the exact source path and
locations; it does not suppress a warning class. Earlier single-side
exploratory logs and source copies match their retained files, and no other
module warned. This is author-only exploratory evidence, not a paired build.
The policy's normal synthetic controls exited 0 and its optimized invocation
was rejected. The independent fake compiler/dependency loop exercised all 10
planned side/module steps and rejected missing, changed and extra warnings,
wrong client axiom name, missing same-side project import, and wrong dependency
output. Separate bad-pin, existing-output and optimized-interpreter guards
passed. These controls do not compile Lean or prove the graph theorem.

The reviewed sampled monitor's actual harmless-child RSS, exception and
external-SIGTERM controls also exited 0. They cover the tested verified leader
and same-group descendant, not escaped descendants; sampled leader RSS and disk
checks are not hard process-tree quotas. Separate `--deps` and audit
subprocesses have ordinary timeouts, not the monitor's RSS/group controls.

A real pair is conditionally ready only in a trusted clean **initial** native
loader/interpreter environment and an externally enforced stable-HEAD,
sole-Lean window. The driver itself does not enforce Git HEAD stability and
stripping child variables cannot retroactively protect the initial Python
loader. A post-build audit must inspect the actual outer exit, all 10 source,
object, log and import rows, the four exact warnings on each side, and the
exact axiom report, while retaining the graph and iPRA limits.

Run from the repository root under a trusted clean initial loader environment:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-saturation-client-prelaunch-audit/audit.py
```

The reviewer uses original `/tmp` provider trees and fails closed if its
pinned inputs change or disappear. See `CHECK.json` and
`terminal-observation.json` for actual observed outcomes.
