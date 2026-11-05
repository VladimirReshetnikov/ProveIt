# Package 65 reverse-direction captured provider

The 62 source modules needed to build `P65Facts.halts` were compiled with
Lean 4.32.0 in the recorded captured environment. The resulting theorem
says that a positive package-65 graph zero at the fixed compact44 ports
produces an internal halting time for machine 215 in every model of IΣ₁.
Its `#print axioms` output is `[propext, Classical.choice, Quot.sound]`.
The theorem's exact statement and proof are in the canonical
`Lean/DiophantineConsistency/Compact44/P65Facts.lean` source. The graph
import is mapped to the same `P65GraphShim` object used for the separately
checked halt-to-zero direction, avoiding duplicate declarations.

This is a captured-provider build, **not** a clean rebuild of the entire
current source tree or an iPRA proof-existence theorem by itself. Each shim
is the pinned canonical source with only import lines rewritten to the
recorded available module paths. The separately checked graph shim has an
import-only substitution documented in `research/p65-halt-converse-algebra/`.
The direct imported captured objects are hashed, but their full transitive
source/object ancestry is not authenticated here. A canonical-source replay
and the final model-to-iPRA bridge remain separate obligations.

**Subsequent source drift.** After this replay, the merge of origin commit
`e1b79c42eb` changed the current `Compact44/P72Exact.lean` and
`Compact44/P72Power.lean` sources. The manifest retains their historical
hashes `283cfc85…` and `8359cee0…`; current hashes are `b4d73644…` and
`f46584fb…`, respectively. The recorded run is evidence for the pinned
versions, not a replay of those later edits. Its historical manifest checker
still rejects the changed source. A later [post-merge replay](../p65-post-merge-replay/README.md)
forced recompilation of the affected closure visible in the recorded
manifests, including `P65Facts` and the endpoint. That replay inherits the
captured providers and their unauthenticated transitive ancestry; it is not
a clean rebuild of all current canonical sources.

`manifest.json` pins each of the 62 canonical source files, its generated
shim, the exact import substitutions, and 62 selected baseline object files.
`results.json` pins the 62 successfully built objects and per-module logs.
The build uses a symlink overlay under `/tmp/p65-reverse-provider/lib` to
avoid Lean's first-module-prefix search masking the captured provider.
It does not modify the provider. The `.olean` objects remain in `/tmp` and
are deliberately not committed; the paths and hashes document the specific
local run rather than promising that those temporary files persist.

The final compiler run for `P65Facts` exited 0; see its log. The first
`P65Root` attempt exceeded the 3 GB Lean memory limit; its failure log is
preserved as `P65Root-failed-M3000.txt`. The exact unchanged source then
passed under `-M6000` with a 300-second per-module timeout. Four earlier
modules passed at `-M3000` and were reused after hash verification. The
full builder completed and a cached replay exited 0. The checker and audit
passed. The only successful-build warning was the existing unused `hv`
linter warning in `Facts.FreeJPowerCancel`; it is retained in the log.
Source scans found no `sorry` or `admit`, and the audit found no `sorryAx`,
unexpected compiler warnings, nonzero module exits, or unexpected printed
axioms. Source scanning and printed axioms do not establish the provenance
of already compiled dependencies.

To reproduce in the same captured environment from the project directory,
copy the four scripts to their documented `/tmp` names, run the preparation
script, create the overlay, run the manifest checker, the sequential builder,
and the audit. All paths are environment-specific; retain a prior result
only after verifying its source, object and log hashes:

```sh
cp research/p65-reverse-provider/prepare.py /tmp/p65_prepare_reverse.py
cp research/p65-reverse-provider/build.py /tmp/p65_build_reverse.py
cp research/p65-reverse-provider/check-manifest.py /tmp/p65_check_reverse_manifest.py
cp research/p65-reverse-provider/audit.py /tmp/p65_audit_reverse.py
python3 /tmp/p65_prepare_reverse.py
mkdir -p /tmp/p65-reverse-provider/lib
cp -asn /tmp/trace74-direct-four-block-1zltaw2f/lib/. /tmp/p65-reverse-provider/lib/
cp -asn /tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib/. /tmp/p65-reverse-provider/lib/
python3 /tmp/p65_check_reverse_manifest.py
python3 -u /tmp/p65_build_reverse.py
python3 /tmp/p65_audit_reverse.py
```

The builder records its actual command, exit status and output per module,
checks the manifest before running, and reuses a cached module only when its
recorded shim and object hashes match. It stops on the first compiler error.
`audit-result.txt`, `manifest-check.txt`, `cached-replay.txt`, and `logs/`
record the run. In particular, the cached replay validates existing object
hashes and does not claim that those objects were rebuilt during that replay.

```text
manifest.json     9cc6b449e9da05cc022386f316c88a5a1d854f21e205aab9c13a2e076fddc4e1
results.json      d8a8c804137ab7910b62356cd398eab9f6b30742155d1e43d05f29a11203aa0a
prepare.py        679ff568711b795b22117e4416c317122e5ffd89117d4b8c9f69b71deb7dab96
build.py          547d2dece206e9aa3fa9165bde305729016f8b8ba947e319cc00ec58d3971584
check-manifest.py 8a0b34b535dfd5b304e7650fcc796b5e6147456d15da1741efbf5a96163e4b95
audit.py          7d8ac0b9ef4951a0e53316e94f376664cc5bd5e6827ae6fd67b677db2091fad9
```
