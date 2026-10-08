# Source provenance and limits of the comparison

Research date: 7 October 2026 (Pacific time). The repository was changing during the
investigation. These are file-level Git blob pins, not an assertion that an entire
repository commit was cloned or reproduced.

Repository: `VladimirReshetnikov/ProveIt`.

| Inspected path below `Topology/UnknotRecognition/` | Git blob |
|---|---|
| `fast/fastunknot/scan_fast.py` (interruptible-current API) | `6c731d0f4d2c2c8bbe513e6b7495cf5dbdc8dc88` |
| `fast/fastunknot/planar.py` | `1078526e7e7dbaf0b7267728105d870d94136769` |
| `fast/fastunknot/geometry.py` | `96acc160dbf2df7981b2db98b602311712a01531` |
| `synthesis/radical.tex` (existing theory and geometry warning) | `53da077349498476001f6b45065b34f0e029daa6` |

The initial inspection of `scan_fast.py` used older blob
`2c1ad52d14296b109376af19668ae0eebb4c6fdd`. After the concurrent adaptive integration
was observed, the source-derived fixture was updated to the newly inspected
`update_budget`/Boolean-return semantics above. Final timings use that updated
fixture. Earlier exploratory timings are not part of this release.

The fixture's `scan_fast.py` and `planar.py` were transcribed from the inspected
source. The intended executable algorithm is retained, but comments and docstrings
are shortened. This is not a byte-identical copy and no normalized-AST equality
check was executed in the present runtime. `integration/check_upstream_ast.py`
fetches the exact blobs, checks their Git object hashes, strips docstrings, and
compares executable ASTs. It is a release-integration check, not a result claimed
already to have passed.

The fixture's `geometry.py` intentionally includes only `SMOOTHINGS` and `ScanLimit`,
which the two imported scanner modules need. It omits the original slow matching
geometry, memoized wrappers, and other imports. Its scoped AST audit compares only
those two exported definitions. The package initializer is a local fixture file.

The fixture is not a port of the whole repository and is not the production
recognition pipeline. Structural certificates, polynomial filters, component
sharing, saturated weights, richer adaptive policy, input formats, CLI behavior,
Rust, and threaded races are outside this comparison. Their tests have not been
run here. The independent crossing-cube implementation and the module's full
chain-homotopy checker provide additional finite validation, not a substitute for
an upstream integration run or a proof that the transcribed source has no error.

The `openai/math` catalogue was inspected as a possible research lead. No advertised
result from it is used as a theorem in this work. The article cites the original
arc-algebra, cancellation, perturbation, and unknot-detection sources for its
actual mathematical dependencies. The sharp radical and scalar-survivor material
is credited to the existing maintained ProveIt synthesis as well.
