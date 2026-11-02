# Conditional free-J saturation client: uncompiled draft

This file has a **single-side exploratory check**, not a paired replay. It combines the audited
free-J population graph theorem with the existing four-block identity and
repeated-mask population theorem. The graph zero, positivity and β ≥ 46
hypotheses remain explicit, as do `q = 2^(dN)`, `J = rep(d,N)`, the high-port
split, both mask bounds and residues, their exact population sum, and the
positive high-mask product. The intended conclusions are two no-carry
statements. The draft does not establish the compact44 port tuple, these mask
facts, the symbolic-to-retained port identity, machine simulation or PRA.

A point-in-time four-module source-closure scan is recorded separately in
`free-j-saturation-closure-plan`. The source has not yet passed a source-frozen matched replay and independent
artifact audit.

The author-side exploratory wrapper session 72376 exited 0 for all five
modules. ArithmeticBinaryCarry emitted four linter warnings (two
`unnecessarySimpa`, one `unusedTactic`, one `unreachableTactic`); its exact
log and all other compiler logs are retained. The conditional client had no
warnings or sorryAx. The result remains single-side exploratory evidence.

`warning_policy.py` is a proposed exact-text policy for a future replay. It
accepts the complete observed four-warning output only for the same module and
source path, rejects changed, missing or additional warning text and rejects
warnings in other modules. It does not suppress a linter class. Synthetic
controls exited 0 under isolated normal Python and rejected isolated `-O` with
exit 1. The policy and any future build driver require independent review before
a protected paired build.

`replay.py` is a proposed source-frozen paired driver: it pins the independent
population-provider and four-module closure audits, rebuilds the four missing
modules and this client separately on the same-side provider overlays, verifies
source hashes and exact direct imports, and checks the named client axiom
report. It strips Python-related variables, `LEAN_SRC_PATH`, `LEAN_SYSROOT`, `LD_LIBRARY_PATH`, `LD_PRELOAD`, and `LD_AUDIT` before
compiling. The sampled leader/process-group
monitor is not a hard whole-tree quota; the separate `lean --deps` and read-only
audit subprocesses use timeouts without that monitor. The driver and warning
policy require independent prelaunch review and a protected paired run; no
such run has occurred.
