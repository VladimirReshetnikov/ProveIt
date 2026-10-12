# New work and reused dependencies

The source checkpoint is recorded in `source_checkpoint.json`. The complete
article distinguishes proved statements, implemented operators, finite evidence,
and outstanding global hypotheses.

## New mathematical work developed in this continuation

- Local cancellation-profile product theorem and complete component-sensitive
  vertex-disc discovery bound, including its homogeneous exceptional case.
- Certified fifteen-tetrahedron disconnected cancellation example and exact
  finite minimum-support analysis.
- Proper-boundary interval-bundle relative one-handle theorem, free-product
  condensation, handlebody and ball criteria, and one-two-handle saturated residue.
- Component-cycle marked kernels and polynomial reblocking for every tile whose
  components meet both interfaces, with original edge-address lifting.
- Exact universal connected-tile repetition cutoffs at all nonnegative thresholds.
- Explicit parameter and execution-tree accounting statements for the global goal.

The report credits classical ingredients and prior results. “Developed in this
continuation” is not a claim of exhaustive publication priority.

## New implementations

- `cancellation/fastunknot/normal_weight_clusters.py`
- `geometry/code/unsaturated_bundles/finite.py`, `replay.py`, and `native.py`
- `code/routed_patterns/` including independent routing and reblocking checkers
- New tests, audit drivers, exact fixtures, measurements, and reproduction runner

## Reused material

- `code/pattern_kernel/` is copied unchanged from the incoming four-copy package.
  Its tile types, finite cubic graph certificate engine, independent graph replay,
  and small-instance marked-signature oracle are not new implementations here.
- `cancellation/fastunknot/normal_vertex_gate.py` is the unchanged incoming
  cancellation package's `artifacts/edge_discovery/vertex_gate.py`.
- `cancellation/runtime/fast/` contains the 42 copied transitive dependencies
  identified in `cancellation_dependencies.json`, plus minimal namespace shims.
- `geometry/vendor/` contains the 30 copied transitive incoming modules and source
  corpus identified in `geometry/evidence/upstream_dependencies.json`, plus minimal
  namespace shims.
- `cancellation/runtime/synthesis/data/coherent-obstruction-certificate.json`
  is the pinned maintained source used to derive the new fixture by verified moves.

Dependency namespaces are separate because the two incoming extensions do not
have identical import requirements. Copied module bodies are unchanged; the
small generated `__init__.py` files make these isolated reproduction environments
without importing the maintained recognizer's unrelated public facade.

No remote repository mutation or maintained recognizer default change was made.
The article and `integration/INTEGRATION.md` specify the proposed integration.
