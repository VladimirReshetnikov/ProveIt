# Proposed same-witness saturation paired replay

This is a **prelaunch driver**, not a successful build. It proposes fresh
corresponding author and peer overlays of the audited graph-derived-radix
provider and compiles the three pinned sources in the reviewed closure order:
`FreeJGraphCongruenceExplore`, `CompactSymbolicGraphSaturation`, and
`CompactSameWitnessSaturation2`. The last source's two imports must resolve
to the newly emitted objects from that same side. In particular, the first
source is the extended same-witness version, not the older shorter source
with the same Lean module name.

The driver pins and reruns both the independent closure review and the full
independent graph-derived-radix parent audit before and after compilation. It
freezes all three source bytes and checks their hashes, imports and non-symlink
status before each child and after the final audits. It checks actual direct
object existence and their companion slots, forbids collisions in every output
slot before compilation, and requires an ordinary non-symlink output `.olean`
with no other output companions after each child. All direct and output slot
snapshots are rechecked after later children and after the final parent
callback. Output-directory symlinks, mismatched source bytes, dependency paths,
compiler exits, warning/admission text, exact per-module declaration names or
axiom sets, and mismatched corresponding outputs cause rejection. Lean's
recorded dependency behavior can list Init once or twice; duplicate non-Init
paths are rejected.

`--verify-only --expected-head <40-hex-HEAD>` performs the pinned source,
closure and parent-audit preflight without creating a build output or launching
Lean. A real build additionally requires a fresh direct
`/tmp/ipra-same-witness-saturation-pair-*` output path and the same explicit
HEAD argument. The initial interpreter and native loader must start in a
trusted clean environment with loader injection variables absent; sanitizing
child environments cannot repair an already-injected initial process. A
protected stable-HEAD and sole-Lean window and independent exact-byte
prelaunch review are required before any build.

The inherited compiler monitor samples resource use, limits each child to
600 seconds and a sampled 3.5 GiB RSS ceiling, and samples a 4 GiB free-space
reserve. These are not continuous resource guarantees. The separate
`lean --deps` calls have only a leader timeout, and parent audit subprocesses
are not covered by the compiler process-group monitor. Package-transitive and
dynamic ancestry remain inherited boundaries.

`fake-controls.py` replaces compiler, dependency and parent operations with
fakes; it does not establish a real build. The retained output shows a
six-child good run, a no-output verify-only run, the duplicated-Init success
case, and failure cases for the exact report/axiom schema, warnings/admissions,
exit and interruption flags, missing imports, duplicate non-Init paths,
peer mismatch, parent or HEAD drift, frozen-file and directory symlinks, late
changes, and pre-existing/new/late output companions. It also checks all nine
non-object companion suffixes both before and after a fake child. The driver
and harness reject optimized Python. The real read-only preflight session 46141 exited 0 at its recorded HEAD;
its output and terminal observation are retained separately. That observation
does not assert continuous input protection or authorize a later build.

Even a successful pair would concern fixed symbolic beta and masks, arbitrary
natural K, a positive literal graph zero and its shared N and w. It would not
bind retained port bytes, derive the graph-specific weighted cyclic-word and
carry premises, instantiate the compact decoder, establish machine
correctness, or prove an internal iPRA theorem.
