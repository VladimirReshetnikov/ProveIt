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
