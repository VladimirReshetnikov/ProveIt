# Free-J 88-operation draft: retained provider survey

This is a **read-only, point-in-time source and provenance survey**, not a
Lean build, `lean --deps` trace, collision-proof overlay, or launch approval.
It studies the independently reviewed but
[uncompiled free-J 88-operation draft](../ordinary13-freej88-lean-draft/README.md).
No Lean process or build tree is created.

The narrow observed single-provider route uses the retained audited P72 PASS
extension and its inherited fresh base. It leaves two current project
sources, `Compact44.FreeJ13` and `Compact44.FreeJ13Halt`, plus the three new
draft clients. One topological order is:

1. `Compact44.FreeJ13`;
2. `P88PairGraph`;
3. `Compact44.FreeJ13Halt`;
4. `P88PairModel`;
5. `P88PairEndpoint`.

The graph client and `FreeJ13Halt` may be exchanged after `FreeJ13`.
The direct source imports reach five P72 frontier objects:
`FreeJSumSquares`, `FreeJSignedTransport`, `FreeJGraphAuxiliary`,
`QCube92Halt`, and `IPRAOrdinary12Chain`, all in `Compact44`. The declared
external import is `Mathlib.Tactic.LinearCombination`; `Init` is also
observed from the guarded toolchain/package route. `IPRAOrdinary13` need not
be built by this proposed route: the draft uses the same existing
`FreeJ13Halt.positive_model_iff` and `IPRAOrdinary12Chain` adapters directly.
Actual direct imports and path resolution still require a guarded Lean run.

The survey reruns the independently reviewed
[P73/P72 provider inspector](../ordinary13-p73-provider-preflight/README.md),
which rechecks its captured P72/base source, object, log, edge and companion
routes. The five free-J frontiers are explicitly checked as a subset of its
six-endpoint frontier. Reconstructing the narrower recorded graph from the
pinned P72 archive and base records gives 616 P72 objects, 918 base objects,
1,728 P72 and 2,647 base direct edges, and 51,840 P72-direct plus 9,180
base-output guard slots. These are **recorded direct paths**, not a complete
package-transitive or dynamic-load trace. The prior inspector additionally
checks its recorded base input-companion guards and reports no route issues
at this observation.

All five frontier objects were rehashed at their P72 paths against the prior
audited observation. The five proposed target module names had no observed
artifact among 13 suffixes in the P72, base, package, toolchain and project
build roots; the target source names were absent in the P72 snapshot tree.
This does not inspect a future output root or prove actual Lean search-path
behavior. Do not merge separate FAILED-parent roots merely on source equality:
the [prior P73 survey](../ordinary13-p73-provider-preflight/README.md)
records different `ModelDifferenceRing` objects for the same source across
those roots. Their parent status remains FAILED.

## Reproduce

From the repository root:

```
python3 -I -S -B Computability/DiophantineConsistency/research/ordinary13-freej88-provider-survey/inspect.py
```

The frozen [observation](observation.json) records one run. The inspector pins
the prior provider/source reviews, retained P72 archive and base state, and
all three draft files; reruns the prior read-only inspector and draft
preflight; checks source imports, current HEAD tracking and clean draft bytes;
reconstructs both the five-frontier and prior six-frontier route sets; and
checks that the former is a subset of the paths just revalidated by the prior
inspector. It uses bounded subprocesses and emits JSON to stdout. Availability,
HEAD and free-space samples can change; they are not reserved.

The frozen `/tmp` free-space sample is approximately 5.03 GB, below the
5,100,000,000-byte sampled stop. The line-based source import walk is not a
Lean dependency trace, and transient changes, external package-transitive
imports, dynamic loading, future overlay collisions and elaboration/resource
behavior remain unproved. A later isolated runner must reauthenticate actual
source/object/companion routes and collisions, enforce the existing disk,
memory and time limits, obtain independent prelaunch review and exclusive
Lean-slot allocation, and preserve previous artifacts. The prior author-side
parent endpoint is not a paired replay. The external all-signed-integer
equivalence, compact44 file bytes and JSON/PDF binding remain separate; this
survey proves no new Lean theorem or consistency statement.
