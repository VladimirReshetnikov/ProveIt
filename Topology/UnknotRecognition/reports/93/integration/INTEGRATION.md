# Proposed ProveIt integration

## Baseline

This package targets commit `704600626606a9097cfd89d4e3d2bbc63c8dd1cb`.
The code and experiments use the exact unmodified modules inventoried in
`native_snapshot/SOURCE_MANIFEST.json`. The package is additive and has not
changed a maintained recognizer or pushed a repository commit.

The complete archive can first be placed in `docs/incoming/`. For maintained
development, the following mapping is proposed; it requires the small import
adjustments listed below and should retain the delivered differential tests.

| Delivered file | Proposed maintained location | Purpose |
|---|---|---|
| `code/unused_handles.py` | `fast/fastunknot/source_unused_handles.py` | Source decomposition, geometric replay, exact diagram wrapper |
| `code/attachment_kernel.py` | `fast/fastunknot/unused_attachment_kernel.py` | Rooted-forest graph producer |
| `code/attachment_kernel_verify.py` | `fast/fastunknot/unused_attachment_kernel_verify.py` | Independent graph checker |
| `code/native_moments.py` | `fast/fastunknot/parallelity_boundary_moments.py` | One-census native compiler and packet adapter |
| `code/native_moments_verify.py` | `fast/fastunknot/parallelity_boundary_moments_verify.py` | Independent source-bound replay |
| Literal oracles, fixtures, audits and benchmarks | `fast/normal_orbit_research/` or a dedicated research subdirectory | Reproduction and comparisons |
| Article sources and final PDF | A new research subdirectory beside the current synthesis articles | Proofs, scope, further research |

All paths in the right column are relative to `Topology/UnknotRecognition/`.
The proposed names are a mapping for the repository reviewer; the delivered
files retain their standalone names and run together immediately.

## Import and API work required by that mapping

1. Update callers' imports of `attachment_kernel` and
   `attachment_kernel_verify` to the chosen maintained module paths. The
   `kernel_from_decomposition` adapter is defined inside the producer module
   and needs no internal cross-module import change; the independent graph
   checker does not import the producer.
2. Port test and benchmark imports to the chosen maintained names. Keep the
   independent native checker free of imports from the native producer.
3. Replace the snapshot import path in the test runner with the maintained
   `fast` directory. Do not copy `native_snapshot/` into the maintained runtime.
4. Recheck private source helpers against the target revision. They are
   intentionally pinned here. The exact dependencies are visible in each
   new module and described in `unused_handles.md` and
   `../code/native_moments_README.md`.
5. Preserve geometric occurrence multiplicity. A signed incidence coefficient
   cannot replace the degree counter used for unused-handle detection.

## Status and authority contracts

`decompose_unused_handles` returns a decomposition, never an unknot verdict.
Its input may be reducible. Its numerical `cycle` signature is not sufficient
to infer a solid torus. `verify_unused_handle_certificate` verifies only the
source-bound geometric decomposition.

`compile_diagram_initial_core` derives the canonical exterior from the exact
classical one-component diagram. `verify_diagram_initial_core` independently
checks diagram and exterior provenance before using irreducibility. The
positive status is `UNKNOT`. `ADMISSIBLE_CORE` is an intermediate inherited
handle presentation and may still be a solid torus; it is not a negative knot
verdict. A cap yields `INCONCLUSIVE`.

The graph adapter is deliberately lighter: it does not call the geometric
checker. Its SHA-256 value binds only Euler labels and edge incidences.
Retain the verified source packet when giving the graph a topological
interpretation. Arbitrary later boundary patterns cannot be discarded by
the unmarked ball-absorption theorem.

`normal_parallelity_moment_words` produces an operation status, not a knot
status. Its new `unmarked_edges` gap field is exact. Removing only that
field recovers the maintained full native skeleton on the audited interface.
It returns local fibre flips, not a coherent global fibre orientation over a
nonorientable base or arbitrary boundary-pattern transport. The optional
packet wrapper retains upstream base profiles and passive multiplicities;
its verification includes the upstream proof cost.

The pair codec's global inventory check is part of its proof contract. Keep
strict integer validation, positive discriminant, parity/range checks, active
row multiplicity one, complete unique label coverage, and consistent deck
pairing. Do not replace exact integer square roots with floating-point roots.

## Recommended first opt-in use

The source compiler can be evaluated at the existing source-handle stage.
An accepted positive certificate is immediately usable after the diagram-bound
checker. Feeding an `ADMISSIBLE_CORE` to later surface search requires the
normal-coordinate adapter identified as an open task in the article. The
current code does not supply a fresh triangulation of that core.

For native boundary queries, add a differential option that runs both
implementations and compares `native_projection(new['skeleton'])` with the old
complete skeleton. The included exact tests provide a starting bank. Keep the
four-field codec as a differential arithmetic reference. A future cost-based
dispatch can choose between valid operators, but the current measurements
do not justify a universal new default on performance grounds.

## Verification that should accompany integration

Run the included suite against the target maintained modules, retain both
reducible controls, and rerun the specific upstream tests for source-handle
reduction and parallelity boundary words. For a subsequent recognizer change,
measure completed whole-recognizer queries on a separate source-identified
corpus, including timeouts. Do not count an inconclusive local result as a
negative recognition result.

The delivered package has completed its own source and certificate checks.
An integration at a different source revision is a new compatibility change
and should be reviewed as such. No global quasipolynomial claim is authorized
by importing these local modules.
