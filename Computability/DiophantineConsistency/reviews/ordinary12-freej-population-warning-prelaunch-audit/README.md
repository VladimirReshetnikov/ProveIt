# Reviewed exact warning correction before retry

This reviews driver `189b41c279`, SHA-256
`ab21a262ef9ba39ba3c6dc57e1899bc8f2574231e2f1222171b547c37699d725`, and
its retained first protected attempt. It supplements the original conditional
prelaunch review `e7a0c44f8e`; it starts no Lean compiler and is not evidence
that the proposed graph client compiles.

The recorded first wrapper session 52770 exited 1. Its first six author
compiler logs are empty; the seventh, `ArithmeticBinomLegendre`, contains the
single `unnecessarySimpa` warning at frozen source line 78:10. The archived
logs match the original `/tmp` logs, all seven frozen sources match their
pinned closure hashes, seven corresponding objects exist, and no peer output
or paired receipt exists. The packet reports that the seventh Lean child
itself exited 0; the wrapper rejected its warning. This failed run is not
proof evidence. The archived previous driver matches the earlier reviewed
SHA `793a6873...`.

The entire executable difference from that driver is a warning predicate and
its use in the compiler guard. For the exact `ArithmeticBinomLegendre`
module, the predicate accepts **only** the complete observed warning text,
including that run's frozen source path, line, column and linter note; it
rejects a missing, changed or additional warning. Other modules must have no
`warning:` text. No linter is suppressed, and `error:`, `sorryAx`, unexpected
axiom names and counts remain rejected. The eventual successful build must
report this one accepted warning rather than claim warning-free logs.

The revised exact driver's real read-only `verify()` preflight passed against
the pinned closure and power parent. An independently adapted fake-compiler
loop exercised all 22 planned steps and rejected wrong axiom reports,
unexpected warnings, missing same-side project imports, altered dependency
output, and missing/changed/additional copies of the allowed warning. The
packet's own warning controls passed normally and rejected optimized Python.
These checks use fake compilers and dependency queries; they do not prove the
Lean result. The prior review's real-child sampled-monitor controls remain
applicable because the monitor and all other driver bytes are unchanged.

A retry is conditionally ready only in a trusted clean **initial**
interpreter/loader environment and an externally enforced stable-HEAD,
sole-Lean window. Start/end source and provider checks are point-in-time;
package-transitive/dynamic ancestry is not completely authenticated. Sampled
RSS is not a hard process-tree quota, and separate `--deps` and audit
subprocesses lack the monitored RSS/group bounds. An independent post-build
audit must check actual outer/child exits, all 22 objects/logs/imports, the
one accepted warning on each side, exact axiom reports and the remaining
compact44 graph/iPRA limitations.

Run from the repository root in a trusted clean initial loader environment:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-population-warning-prelaunch-audit/audit.py
```

Actual read-only audit session 16755 exited 0. It uses original `/tmp` inputs
and fails closed if pinned inputs or retained failure artifacts change.
