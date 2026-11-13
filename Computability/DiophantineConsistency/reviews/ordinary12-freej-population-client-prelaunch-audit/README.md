# Conditional no-build prelaunch review

This reviews the exact replay driver committed `d27dd1f81a`, SHA-256
`793a6873afd3517b85828e54421ee16cbd6077091b08318fb6bc62611d20de8f`,
and its pinned uncompiled client sources. **No Lean build has been performed
by this review.** The drafted graph client is intended to conclude the
population bound under the positive free-J graph zero, its three port
inequalities, `p₀≥46`, and the explicit radix equality
`1+v₀p₀=2^h`. Whether it actually elaborates and type-checks remains for the
paired build. Its claimed scope excludes retained compact44 port binding,
checker calibration, machine simulation and an iPRA endpoint.

A read-only invocation of the exact driver's `verify()` completed successfully
in session 37378: the source-only closure and audited free-J power parent
passed, covering nine planned sources and 97 base `.olean` paths per side.
The wrapper freezes all nine source files and both client files into its new
output tree, verifies their pinned hashes, and now reads the two client import
lists from those frozen bytes. It refuses to resolve a missing project import
from the external package path. It checks each source and direct `--deps`
result, rejects warnings/errors/`sorryAx`, requires the exact two client axiom
report names and allowed axiom sets, compares sibling outputs, and repeats
parent/source checks afterward. The package and other dynamic/transitive
provider ancestry are not completely authenticated; parent checks and hashes
are point-in-time checks rather than a continuous guarantee.

`mock_loop.py` imports the exact pinned driver and substitutes a fake compiler,
fake dependency query and fake preflight; it launches **no Lean child**. Its
actual final-driver run exited 0 and exercised all 22 planned child steps. It
also rejected a wrong axiom declaration (after 10 fake children), injected
warning (1), missing same-side project import (11), and wrong dependency
output (1). These controls test wrapper branches, not compilation or
mathematical correctness. `guards.py` separately checks an incorrect source
pin, an already-existing output directory, and optimized Python rejection;
its actual run exited 0. The exact reviewed sampled monitor's own real-child
negative controls, run in session 68926, exited 0: persistent missing RSS,
transient/exit races, monitor exceptions, and external SIGTERM. The exercised
cleanup covers its verified group leader and tested same-group descendant,
not processes that escape that group. The monitor samples the leader RSS and
free disk and uses a per-child time limit; it does not impose a hard
whole-process-tree memory quota. Dependency queries and parent audits use
ordinary subprocess timeouts rather than that monitored path.

The intended build is reasonable to launch **only with** a trusted clean
initial interpreter/loader environment, an externally enforced stable-HEAD
and sole-Lean window, and the documented provider limitations. The wrapper
itself does not enforce Git HEAD stability or remove loader influence before
the initial Python interpreter starts. Inherited `PYTHON*`, `LD_PRELOAD`,
`LD_LIBRARY_PATH`, `LD_AUDIT`, and Lean path variables are stripped for
compiler children, but that is not retroactive initial-loader protection.
The post-build audit must verify the actual outer exit, both full 11-step
chains, exact names/axiom sets, direct objects/imports, logs and source pins.

Run this no-Lean review from the repository root in a trusted clean initial
loader environment:

```
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary12-freej-population-client-prelaunch-audit/audit.py
```

The independent reviewer uses the original `/tmp` provider objects; removal
or byte changes fail closed. Hashes and source checks are point-in-time, and
the fake output trees are temporary and removed after each trial.
