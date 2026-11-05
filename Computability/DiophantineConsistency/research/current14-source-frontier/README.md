# Current-source frontier for the historical 14-variable endpoint

The checked historical paired replay of the maintained equation's standard
iPRA endpoint is described in the [terminal record](../../reviews/ipra-standard-current14-historical-pair-terminal/README.md).
This packet records a **source-directed rebuild plan**, not a new Lean
replay or an authentication of the historical provider.

On 2026-11-04, at workspace HEAD `5ef603fecebf94a3b957c1167f74aa6298eeafa4`,
the pinned historical snapshot manifest's declared project import graph for
`IPRAStandardCurrentEndpointChecks` has 1,000 reachable modules. Comparing
its source hashes with the workspace found 13 changed and no missing sources.
The explicit import declarations of all 13 changed files agree with that
manifest. The reverse closure of those 13 nodes within the historical graph
contains 207 modules, including the endpoint check. The complete lists and
both old and current source hashes are in [`result.json`](result.json).

This is a conservative invalidation set for planning a source-current replay;
it is not a claim that 207 newly written theorems are needed, that every
unchanged object can safely be reused, or that a rebuild succeeds. In
particular, exact matching objects and their transitive source, package and
dynamic-loading ancestry still have to be supplied or rebuilt. The earlier
paired run's prepared project object directories no longer exist at their
recorded paths in this workspace. Available alternative providers include
mixed or differently hashed artifacts and have not been authenticated as
replacement seeds by this audit.

## Reproduce the source comparison

From the repository root, run:

```sh
python3 Computability/DiophantineConsistency/research/current14-source-frontier/audit.py
```

The script reads the pinned [`historical-manifest.json`](historical-manifest.json)
and the committed historical replay preparation record. It checks their
SHA-256 hashes and their linkage, recursively follows manifest-declared
project imports from the endpoint check, hashes the current workspace files,
checks import declarations for changed sources, and computes the reverse
closure on that historical graph. It writes JSON to stdout without modifying
files; the committed [`result.json`](result.json) is the captured observation
at the HEAD above. Python optimized mode is rejected.

The result is valid only for the recorded historical manifest and workspace
state. It does not parse arbitrary Lean module syntax, prove the source
semantics, run Lean, inspect runtime module loading, or certify external
packages. Future source changes require rerunning it; import drift or missing
sources make the historical-graph closure insufficient for a current-source
build plan.

As a separate cross-check, the author rederived the same 207-node reverse
closure from the retained `strict-plan.json` (SHA-256
`e21d3d303922ffaa21151c490ce093e06bfdb65a43cf6fd55befd831c2f62c82`)
and compared the resulting module set with `result.json`; this matched. It
was not an independent reviewer or an additional Lean build.

## Local seed-byte availability observation

On 2026-11-04 a separate read-only scan considered the 793 manifest
ancestors outside the recorded 207-node affected closure. Among the five
explicit temporary provider paths in [`scan_seed_objects.py`](scan_seed_objects.py),
it found bytes matching the historical author-seed SHA-256 for 489 modules;
304 had no matching bytes in those five locations. Its captured
[`seed-scan-result.json`](seed-scan-result.json) lists the matches and
unmatched modules. All five providers are machine-specific and can change or
disappear. The scan did not look everywhere, guard against transient file
mutation, authenticate source-to-object ancestry, or inspect external
packages; an unmatched result is not proof that an object is unavailable
elsewhere. Matching individual object hashes is not by itself a coherent
replay provider.

The scan can be repeated from the repository root with
`python3 Computability/DiophantineConsistency/research/current14-source-frontier/scan_seed_objects.py`.
It reads hundreds of object files and may take time. It uses the pinned
historical preparation record and the recorded source frontier; its output
reflects the local providers at the time of the rerun.
