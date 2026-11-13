# Carrier65 retry05 continuation: source-only design

This is a **design and abstract record projection**, not an executable build
runner or permission to launch Lean. The reviewed [prefix feasibility
inspection](../current14-carrier65-retry05-prefix-feasibility/README.md) found
239 retained outputs and 1,000 retained base links with matching recorded
bytes and guards, but did not establish full transitive provider coherence,
companion requirements, filesystem immutability, or actual Lean resolution.
The original [retry05 runner](../current14-coherent-extension-refactor-retry05-runner/run.py)
requires a fresh fixed output and must not be restarted against, modified in,
or used to overwrite its preserved failed root. Current free space must also
exceed the established stop floor before any future guarded build.

An [independent review](../../reviews/current14-carrier65-retry05-continuation-design-independent/README.md)
reconstructs the recorded projection and checks the design's stated limits;
it does not certify provider compatibility or a runnable continuation.

## A concrete candidate arrangement

A new, separately reviewed program could create a **fresh private root** with
its own `src`, `lib`, `logs`, state and terminal receipt, leaving the old root
read-only and unchanged. In one possible layout its `lib` contains 1,000
links to the recorded base `.olean` producers and 239 links to the old prefix
`.olean` files, while all other recorded output suffixes remain absent. Its
`src` contains verified copies of the 529 pinned source files and the final
audit client. New outputs for the 290 remaining stages and the audit client
would be regular files under this new root, never under the retained root.
A link to a prefix object is a **reused input**, not an output produced by the
continuation. A verifier must distinguish these categories: the original
postflight rejects symlinks for its own outputs and cannot simply be rerun
unchanged on this layout.

The read-only `project_recorded_routes.py` makes no directories or links. It
uses an abstract `@NEW_LIB@` label to project the saved guards onto that
hypothetical layout. From the pinned failed state it checks that the 1,239
proposed link names are distinct and do not overlap pending planned outputs;
all 9,308 recorded old-root dependency-guard entries project to the same
recorded presence, target realpath and hash, including recorded absences. It
also observes 373 recorded dependency paths that would be relabelled to the
new root and 343 that would retain their external spelling. The 18,616
external guard entries are carried from records, **not reauthenticated** by
this projection. There is no projected Lean invocation or check that Lean
will choose those paths. `projection.json` is a mathematical bookkeeping
receipt for these saved records, not a safety certificate.

Symlinks do not freeze their targets. The old prefix objects and base/package
files could change during a future build, and hard links would share the same
mutable inodes. Do not change permissions or otherwise mutate the user's
retained evidence to simulate immutability. A future runner must either use a
separately protected immutable snapshot of the authenticated bytes or prove a
sufficiently strong isolation and pre/during/post revalidation scheme; if it
cannot establish its protection condition, it must refuse. Copying is not
free: at the recorded inspection point the 239 prefix objects total
147,327,432 bytes, the 1,000 base-link targets total 449,864,896 bytes, and
the 530 source snapshots total 2,775,906 bytes. Those figures exclude package,
toolchain, future outputs and filesystem overhead, may change, and are not a
resource reservation or a claim that copying just these files is sufficient.

## Proposed fail-closed state machine

The steps below describe acceptance conditions for an implementation to be
written and independently reviewed; none has been implemented or run here.

1. **Pin and audit inputs.** Authenticate the exact plan, original runner,
   monitor, Lean binary/toolchain, selected source snapshots, failed state,
   outer receipt and historical prefix evidence; rerun independent read-only
   audits without changing those records. Validate all 239 prefix rows, their
   478 child logs, output slots, source hashes, recorded axiom reports where
   applicable, direct routes, and the 1,000 base links. Reject any drift,
   missing record, unexpected object, diagnostics, ambiguous producer or
   inconsistent guard. Reauthenticate the base producer history, package and
   toolchain objects **and their transitive/implicit/runtime dependencies**,
   including the actual companion files Lean requires. The recorded 716 direct
   edges and 13 suffixes alone do not complete that task.
2. **Secure resources and exclusivity.** Establish an enforceable exclusive
   build slot and the recorded resource monitors before allocating outputs.
   A cooperative lock and a `/proc` scan alone cannot exclude unrelated Lean
   processes that ignore the lock or race the scan; the implementation must
   document and verify its actual isolation boundary or refuse. Keep the old
   guard limits: disk strictly above 5,100,000,000 bytes, host available memory
   at least 10 GiB, sampled child-session RSS below 4 GiB, `-M3600 -j1
   -DElab.async=false`, at most 180 seconds per child, and a six-hour global
   deadline. To avoid silently extending the original deadline, this design
   conservatively counts the recorded 2,487.332 seconds from retry05 against
   that six-hour budget, rounding upward if using integer time. Monitoring is
   sampled and therefore does not prove that transient spikes cannot occur.
3. **Create and recheck the private layout.** Atomically claim a previously
   nonexistent root and use exclusive creation/no-follow protections for
   every output and state name. Snapshot the selected sources and authenticate
   all copy bytes. Materialize only explicitly authorized base/prefix inputs
   and required companions with disjoint names; authenticate link/copy target,
   hash, search precedence, absence of every relevant alternate, and the
   chosen immutable-input condition. Preserve original path identities and
   hashes as provenance separately from new root paths. Rerun the full prefix
   and base checks against both evidence and the mapped layout. If any
   required private artifact, runtime dependency or toolchain companion cannot
   be inventoried and verified, stop rather than assuming its absence is safe.
4. **Start at the first unrun stage.** The existing stage-240 row is a stub,
   not a successful build. Initialize a new state referencing the 239 original
   completed rows and their evidence, and put stage 240 in a new row without
   editing the original state. For each planned stage 240–529 and the separate
   final audit client, run guarded `lean --deps` first; require the resulting
   exact dependency set, ordered candidate resolution, realpaths, hashes,
   relevant suffixes and producer identities to match an independently checked
   plan. Treat `Init`'s package/toolchain paths according to an explicit,
   independently verified rule rather than assuming duplicate names are safe.
   Compile only after the dependency check, into a previously absent owned
   destination. Preserve command, environment, logs, child status and guard
   samples. Unexpected diagnostics, missing/extra dependencies, collisions,
   changed inputs, guard/monitor failures or resource refusals stop the run
   while preserving its state; no fallback or automatic unguarded retry.
5. **Postflight all 530 stages.** Recheck every source snapshot, original
   prefix log and output, mapped prefix/base input, new output and companion,
   dependency route and guard, against the appropriate old or new identity.
   Check all originally required intermediate axiom reports and the three
   final-client reports with the existing allowed-axiom policy, and reject
   `sorryAx` or missing/extra reports. Record that 239 stages were reused and
   291 were newly attempted; do not label the old stub as passed. An
   independent reviewer must inspect the complete state, evidence and final
   theorem statements before any completion claim.

If a required historic object or provider cannot be authenticated or isolated,
the appropriate fallback is a separately guarded rebuild of the affected
closure; the current information does not identify a sufficient minimum
subset. A full fresh replay still has 529 planned stages plus the audit client.
A continuation's success would concern the checked quoted/formal statements
and documented provider boundary; raw TeX/PDF semantics remain a separate
binding obligation.

Reproduce the **record-only projection** from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/current14-carrier65-retry05-continuation-design/project_recorded_routes.py | cmp - Computability/DiophantineConsistency/research/current14-carrier65-retry05-continuation-design/projection.json
```
