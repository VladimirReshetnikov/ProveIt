# Source-declared closure for the 2011 parent-zero route

This is a **source survey and build plan**, not a Lean compilation, an
actual-zero rank-phase theorem, a complete dependency audit or an iPRA
proof. The immediate planned roots are
`DiophantineConsistency.ArithmeticWindowZero` and
`DiophantineConsistency.ArithmeticRankForcing2011`. They are candidate
interfaces for extracting the current 2011 carrier's block/window data and
rank phase; an additional actual-zero client still has to be written.

[`source-manifest.json`](source-manifest.json) pins the source anchor, every
source-declared direct import and workspace SHA-256, and a dependency order.
It identifies **44 additional project modules** and eight direct imports from
the frozen 70-source parent. In particular five of the additional modules are
in the repository's `FirstOrder` and `PAHF` libraries, not in the
`DiophantineConsistency` namespace. Eight direct external imports resolve to
recorded `.olean` paths and SHA-256 values. The source manifest also pins the
workspace lakefile and Lean toolchain text.

The `Foundation` source root specified by the workspace lakefile is not
present in this environment; this survey deliberately classifies Foundation
imports as inputs from the already used package provider. It does not rebuild
or inspect all transitive package imports, dynamic imports, or compiler
options. Nor does the manifest itself authenticate every parent object: the
separate [70-source parent audit](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md)
records the matched project outputs and its inherited package and original
Foundation-wrapper qualifications. Any actual successor build must use a
coherent fresh out-of-tree overlay, validate parent objects and the new source
snapshot before and after, record actual compiler and wrapper exits, and obtain
an independent review. It must not silently mix historical project objects.
The two post-merge Lean files not in the 70-source parent remain outside this
44-module route unless a later client explicitly imports them.

[`audit_plan.py`](audit_plan.py) checks the frozen source-manifest hash and all
70 parent source hashes against both the workspace and the pinned commit;
reads the `lakefile.toml` library map; recursively follows project imports in
those two roots; and checks that each of the 44 workspace sources equals its
pinned-commit bytes. It resolves direct external imports against the package
provider or the named Lean toolchain and fails on an unresolved direct object.
The resulting order and import lists are source-declared only: Lean's actual
`--deps`, generated companion objects, and dynamic loads remain build-time
obligations. The script uses no assertions for checks and refuses optimized
Python. Its `--write` mode creates a fresh manifest only and refuses overwrite;
the default mode rechecks the already pinned manifest without writing it.

A default recheck actually exited 0 and reported
`PASS_SOURCE_DECLARED_CLOSURE 44 parent-boundary 8 missing-external []`.
An optimized invocation actually exited 1 before the survey. Earlier
exploration estimated 39 by following only the `DiophantineConsistency`
namespace and mistakenly treating `PAHF.PACore` as external; the corrected
lakefile-aware survey adds all five project modules. An initial generator
attempt failed because it incorrectly expected a different source-snapshot
status instead of `FROZEN_NOT_COMPILED`, and the first lakefile-aware attempt
failed because Foundation's local source path was absent; Foundation is now
explicitly treated as the inherited package-provider boundary. The superseded
39-module observation is not build evidence.
