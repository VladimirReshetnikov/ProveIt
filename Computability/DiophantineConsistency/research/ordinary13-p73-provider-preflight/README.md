# P73 91-operation bridge: provider route survey

This is a **read-only, point-in-time provenance and planning survey**. It
does not invoke Lean, compile a client, establish compatibility of the
proposed overlay, or authorize a build. It studies the uncompiled
[91-operation draft](../ordinary13-p73-share91-lean-draft/README.md) and the
existing `P73Graph` / `IPRAPositive73` imports. The P73 author-side endpoint
build and the new draft's proofs retain the qualifications in that packet.

The narrower observed route uses the retained, independently audited
[681-stage P72 PASS extension](../p72-current-base-extension-build-attempt02/README.md)
and its 1,000-object fresh base as one provider root. At the recorded
observation:

| Proposed stage | Current project sources above P72 | P72 frontier objects | Direct external candidates |
| --- | ---: | ---: | ---: |
| `P73Graph` only | 2 | 2 | 1 |
| Existing draft's `IPRAPositive73` route | 7 | 6 | 1 |

The graph-only source order is `Compact44.FreeJ13`, then `Compact44.P73Graph`;
its two P72 frontier objects are `FreeJSignedTransport` and `FreeJSumSquares`.
Their recorded ancestry reaches 13 P72 objects and 17 base objects. This is
the smallest observed staged starting point for the draft's arbitrary-ring
equality, **not** an endpoint by itself.

The existing endpoint draft's seven-module topological order is preserved in
`observation.json`. The six frontier modules are `FreeJGraphAuxiliary`,
`FreeJSignedTransport`, `FreeJSumSquares`, `IPRAOrdinary12Chain`,
`P72Converse`, and `QCube92Halt`, all in `Compact44`. The direct external
candidate is `Mathlib.Tactic.LinearCombination`: its observed hash matches a
historical base direct-input pin, but this is not a full package ancestry
audit. The three new draft clients are additional compilation stages.

A narrower **unimplemented design sketch** would replace the draft model
client's import of `IPRAPositive73` by imports of `P73Halt`, `P73Converse`, and
`IPRAOrdinary12Chain`, then assemble the same positive bridge from the two
existing directions. Its line-parsed cut contains six P73 project sources,
the same six P72 frontier objects, and one external candidate. This would
replace one provider compilation with changed client code; the code has not
been written, compiled or independently reviewed and is not the current
draft. It does not remove the P73 converse dependency.

For comparison, cutting only at the 1,000-object base yields 15 sources and
four base frontier objects for the graph, or 686 sources and 48 base frontier
objects for the endpoint. These counts are source-import planning estimates,
not proved minimal build sizes. Do not merge in objects from successful
children of failed coherent runs merely because source hashes match:
`ModelDifferenceRing` has matching source bytes but distinct recorded object
hashes across the P72 and failed-run roots. Their parent failures remain
failures. The observed single-P72 route avoids that mixed-root choice; its
future overlay still needs a fresh collision and `lean --deps` review.

## Reproduce the survey

From the repository root run:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-p73-provider-preflight/inspect.py
```

The command emits JSON to stdout and requires the retained `/tmp` providers.
The frozen [observation](observation.json) records one run. It pins the
fresh-base manifest, PASS state, independent audit and outer receipt; the P72
PASS progress, source snapshot, independent stage/base/archive audits, outer
receipt and frozen stage archive; and the three draft source files. It follows
the P72 frontier's recorded project routes and checks archived stage rows,
workspace/snapshot/archive sources, logs, object hashes, captured direct
inputs and direct-companion guards. It then follows recorded base project
routes and checks sources, logs, objects, direct inputs, output slots and the
base's recorded input-companion guards. For the frozen endpoint route this
rechecked 679 P72 objects, 1,997 P72 edges and 59,910 P72 guard slots; and
918 base objects, 2,647 base edges and 20,230 base guard/output slots, with
no recorded route issues. The 1,604 relevant workspace source files matched
the recorded Git HEAD blobs in that point observation.

All 1,599 names in the P72 source survey's project-source set occur in the
P72 extension or retained base producer tables. One captured Foundation
dependency, `Foundation.FirstOrder.Arithmetic.IOpen.Basic`, is outside those
project tables: its workspace source is absent and its recorded object route
is the guarded Foundation package overlay. Its direct object hash is checked;
its package-transitive ancestry remains an external qualification.

The declared source walk is line-parsed; it can miss imports produced by
other syntax and is not `lean --deps`. Recorded direct routes, package
transitive dependencies, dynamic loads, changes between observations and
toolchain/runtime behavior are not fully established by this survey. A
future guarded runner must authenticate its actual direct routes, isolate and
check overlay collisions and companions, pin each source and object, enforce
the established 5.1-GB sampled disk stop, 4-GiB sampled child RSS, 10-GiB
host floor and per-stage time limits, and capture actual exits and postflight.
The P72 historical build used different recorded resource caps; its success
does not guarantee a new run fits the current ones. Independent prelaunch
review and shared-slot allocation remain required.

The frozen `/tmp` free-space sample was approximately 5.05 GB, below the
5,100,000,000-byte disk stop. It is not reserved and can change. No earlier
artifact was removed. The prior P73 author build and the P72 base retain
their inherited package/dynamic ancestry limits. This survey does not bind
Lean to JSON, coefficient files or rendered PDFs, or establish either side of
the consistency biconditional.
