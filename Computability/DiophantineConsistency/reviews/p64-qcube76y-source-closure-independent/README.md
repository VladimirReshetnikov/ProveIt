# Independent review of the 76Y source-closure plan

The [source-closure survey](../../research/p64-qcube76y-source-closure-plan/README.md)
was rerun under low CPU and I/O priority and reproduced its retained result.
This review separately recomputed reachability, reverse dirty closure, source
hashes and topological orders **from the stored edges**, without running
Lean. It confirms 42 flat and 1,608 project modules, of which 919 project
sources match the recorded 1,000-module base and 689 are additional. No
shared project source lies in the computed dirty closure, and no declared
project-to-flat edge was found. Both the 689-project and 42-flat proposed
orders are topological relative to their declared predecessors. All 1,650
recorded current source files matched their hashes, were tracked and matched
HEAD at this observation.

The survey scanner classifies an unqualified name absent from its flat-source
index as *external*; it does not generally reject a missing or misspelled
flat import. An unknown dotted import is also classified as external unless
its top-level namespace is mapped to a project source root. In this frozen
result, however, the only dotless external name is `Init`. The 80 declared external names have prefixes `Mathlib` (41),
`Foundation` (37), `Lean` (1), and `Init` (1); a corresponding `.olean` was
present in the inspected package or toolchain root for every name. This
checks file presence, not that Lean resolves or authenticates it. The three
new Mathlib objects were present but had no matching `.olean` path in the
older provider receipt's declared external guard, matching the survey's
warning.

A coherent extension should be **prepared but not launched** until the
current14 base has actually succeeded and its source snapshot, outputs,
companions and provenance have been independently authenticated. The
existing fresh-closure driver starts with no project objects and rejects any
project dependency not in its freshly built set; it cannot directly reuse the
919 base objects. A separate guarded extension driver must explicitly admit
only the authenticated base objects, route the 689 new project objects and
42 flat objects to fresh non-overlapping paths, reject namespace fallbacks and
shadows, freeze all 731 sources, and compare each actual `lean --deps` result
with the declared imports before compilation. It should guard the three new
external objects and companions, recheck all direct inputs, outputs and source
hashes, and preserve terminal exits and axiom logs. Dependency graphs,
package-transitive and dynamic loading, potential source drift, and final
PDF/JSON/gzip bindings remain separate obligations; the 689+42 counts alone
are not a successful build or evidence that old objects can be mixed safely.

[`check.py`](check.py) pins the survey and base manifests and reproduces the
independent stored-graph/current-byte checks. It also records the three new
external object hashes at this observation. It does not independently parse
Lean source syntax, invoke `lean --deps`, rebuild anything, or authenticate
external object ancestry. Temporary package paths and workspace files may
change, so a later rerun can fail. No Lean was run for this review.

```sh
nice -n 19 ionice -c 3 timeout 60s python3 -I -S -B Computability/DiophantineConsistency/reviews/p64-qcube76y-source-closure-independent/check.py
```

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `c857c06486b851269ebd1cbf7972710a713f0a2ec5fef66a99d5b8ce6607a70a` |
| `result.json` | `7850018c9fab10486ff65a8f76f07a2ef5d88b740e5326feaf4bb2862f57fcb9` |
