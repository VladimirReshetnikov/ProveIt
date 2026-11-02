# Pinned preflight launcher (not yet independently reviewed)

`launch.py` is a concrete, fixed-path launcher for the coexistence-only pair
listed in `REAL-RUN.md`. It checks exact script, source-snapshot, compiler,
Foundation/provider and independent-review receipt hashes and their observed
exits. `gates.py` rehashes the full 70-source snapshot and tracked workspace,
1,540 Foundation artifacts, 14,764 declared-provider guard paths and the
three direct Foundation imports, then rechecks source and fixed pins. It
refuses occupied or protected outputs and optimized Python, samples 4 GiB
free-space before launch, and delegates both fresh siblings to the sampled
monitor. It saves a preflight receipt and actual pair-coordinator exit/stdout.

The launcher itself and these controls require separate independent review
before use. The resource threshold remains sampled, not a continuous reserve
or hard quota. Foundation's original outer wrapper exit was not captured;
inner Lake exit and independent provider verifier exit were 0. This endpoint
checks three coexistence axiom reports; it does not prove the signed graph
transport, denominator integrality, checker calibration, or an iPRA theorem.

Read-only preflight session 45404 exited 0 and produced receipt SHA
`1e696fa9113522b6e35cba693d8442878f18692d6c59c0f67657496b4b5e1fa0`.
It started no project build. Toy controls independently reject source and
provider drift, invalid review pins, optimized launch and missing executable
pins; a fake coordinator tests terminal capture and environment sanitization.
Their actual outputs are recorded under `launcher-observations/`. The earlier
runbook's direct coordinator command remains an illustrative command, not a
replacement for this launcher's fail-closed preflight or the review gate.

## Isolated-startup correction

An independent actual-child canary found that the original launcher inherited
`PYTHONPATH`, allowing `sitecustomize` to run before coordinator checks. The
corrected launcher requires the explicit invocation `python3 -I -S launch.py`,
strips inherited `PYTHON*` variables and `LEAN_PATH` from its coordinator
environment, and starts the coordinator with an isolated `-I -S` bootstrap.
The coordinator now starts the monitor, builder and comparator with isolated
no-site startup as well. Direct non-isolated invocation can execute Python
startup hooks before any script-level rejection, so callers must enforce the
shown isolated command externally. Other non-Python environment, executable,
OS, package-transitive and dynamic-load assumptions remain.

The original read-only preflight above is historical. After these corrections,
actual isolated read-only preflight session 73348 exited 0 with receipt SHA
`b4720cc526f2fe19a796ce90a9a646ac73bcd0f66c732525d1d0d166579aabeb`.
An actual-child canary confirmed ordinary Python executes the injected site
hook, while isolated launcher startup and isolated coordinator bootstrap do
not. A separate isolated wrapper-chain review is pinned by the corrected
launcher. The corrected outer launcher itself requires independent review
before any real project build.
