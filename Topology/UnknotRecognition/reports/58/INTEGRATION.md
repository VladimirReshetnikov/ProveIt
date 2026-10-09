# Integration into ProveIt

## Baseline and patch scope

The integration baseline is ProveIt commit
`eb368edf975695e3e16a8774dcb7846bda0c13a0`, under
`Topology/UnknotRecognition/fast`.

The package's `integration.patch` adds the new topology-spectrum runtime,
three focused test modules, and the reproducible research drivers and inputs.
The existing recognizer, its default choices, and inherited runtime modules
remain unchanged. The standalone `code/fast/` snapshot includes dependencies
for reproducibility; use the patch to integrate the new work rather than
copying that snapshot over a newer repository checkout.

The six runtime additions are:

| Module under `fastunknot/` | Role |
|---|---|
| `orbit_transversal.py` | Compile least original orbit representatives as intervals |
| `orbit_transversal_verify.py` | Independently reconstruct and verify the transversal |
| `topology_spectrum.py` | Sparse cover inversion, classification, scaling, and forward-equation verification |
| `normal_topology_geometry.py` | Boundary inclusion, integral Euler/marker weights, and vertex-link classification |
| `normal_topology.py` | Validated direct/reduced topology producer and command-line entry point |
| `normal_topology_verify.py` | Original-source reconstruction and independent certificate replay |

The new test modules are `test_orbit_transversal.py`,
`test_topology_spectrum.py`, and `test_normal_topology_spectrum.py`.

## Apply and review

From the root of the intended ProveIt checkout, first check that the patch
applies to that checkout:

```sh
git apply --check /absolute/path/to/integration.patch
git apply /absolute/path/to/integration.patch
git diff --check
```

If the checkout has evolved since the pinned baseline, inspect existing
implementations of the named new modules and changes to the inherited
geometry/orbit APIs before resolving a conflict. The source-bound format and
normal-arc conventions are part of the compatibility contract.

Run the focused gate and a fresh oracle check from
`Topology/UnknotRecognition/fast`:

```sh
python topology_research/run_tests.py --output topology_research/local_results/tests
python topology_research/regina_audit.py audit \
  --corpus topology_research/data/regina_corpus.json \
  --output topology_research/local_results/regina_fresh.json \
  --recheck-oracle
```

Omit `--recheck-oracle` to use the frozen external answers without Regina.
The research package's root `reproduce.py` provides the additional benchmark,
formula, certificate, figure and article commands in its preserved package
layout. Applying the code patch does not itself install the article or the
recorded result archive. Retain those as the accompanying research record;
the article's relative section and figure paths should stay together.

## Supported input

The runtime validates a finite, compact, connected, orientable triangulated
three-manifold with exactly one torus boundary, together with an admissible
standard normal vector. Each tetrahedron has a row of seven coordinates:
four triangle counts followed by three quadrilateral counts. Matching
equations, nonnegativity and the quadrilateral constraints must hold.

The surface may be empty, disconnected, nonorientable, or have closed
components. Irreducibility is not assumed. Generalized triangulations,
repeated global vertices, and loop edges are supported when the inherited
manifold validator accepts them. Extending the API to more boundary components,
higher-genus boundary, nonorientable ambient manifolds, or ideal triangulations
requires additional geometry work; the mathematical observer's broader
applicability does not bypass the implemented input contract.

## Python API

Run with `Topology/UnknotRecognition/fast` on the Python import path:

```python
from fastunknot.normal_topology import normal_topology_spectrum
from fastunknot.normal_topology_verify import verify_normal_topology_spectrum

answer = normal_topology_spectrum(
    triangulation,
    coordinates,
    reduce_core=True,
    periodic_rule="fine_wilf",
    max_cycles=None,
    record_certificate=True,
)

if answer["status"] == "COMPLETE":
    valid = verify_normal_topology_spectrum(
        triangulation, coordinates, answer["certificate"]
    )
    if not valid:
        raise ValueError("topology certificate failed verification")
    spectrum = answer["topology_spectrum"]
```

Each spectrum row contains `chi`, `boundary_components`, `orientable`,
`multiplicity`, and exactly one of `genus` and `crosscaps`. Multiplicity is
an encoded integer; clients should not expand it into a list of components.
The result also contains total component counts, orientability counts,
boundary-circle count and Euler characteristic for the original supplied
vector. Query statistics may describe a smaller core.

Set `reduce_core=False` for the direct observer. Both modes compute the same
abstract type spectrum. The `periodic_rule` choices `fine_wilf` and `aht`
select the inherited orbit merger rule and must preserve the result.

## Command-line example

From the `fast` directory:

```sh
python -m fastunknot.normal_topology census \
  topology_research/data/klein_torus.json --certificate -o klein_result.json

python -m fastunknot.normal_topology verify \
  topology_research/data/klein_torus.json klein_result.json
```

Verification accepts either a certificate object or a complete result
containing its certificate. Add `--direct` to disable core reduction.
`--max-cycles` bounds the sum of boundary, surface and doubled-surface orbit
discovery cycles; `--timeout` supplies a cooperative wall-clock deadline.

## Resource and certificate contracts

Exhausting the discovery-cycle allowance returns `INCONCLUSIVE`, with its
stage and statistics, and no completed spectrum or certificate. An
inconclusive result is neither an empty surface nor a negative recognition
decision. Validation and certificate transport are not charged to this
cycle counter. The optional `check()` callback is polled throughout the
computation and checker; callback exceptions propagate to Python callers.

Certificates use schema `normal-topology-spectrum-v1`. They bind the original
face records and normalized coordinate vector, including peeled vertex-link
multiplicities and the exact core decomposition. Verification reconstructs
the original input, independently checks the decomposition, replays the
transversal and weighted proofs, verifies the spectrum by forward equations,
and checks restoration to the original surface.

The geometry validator, normal-arc conventions and integer codec are shared
trusted code. Independent replay refers to the certificate arithmetic and
reduction checks; the runtime does not contain a second unrelated
three-manifold engine. The bounded Regina audit separately checks this shared
geometric boundary.

Use the inherited `json_safe` transport for potentially huge integer fields.
It can represent large values as signed hexadecimal strings without altering
Python's global decimal-conversion limit; checkers decode declared integer
fields exactly. Do not coerce them through floating-point values.

## Connection to the full recognizer

This API is an explicit observer of a supplied surface. No outer surface
search or hierarchy procedure is installed by the patch. A disc-type row
counts both meridians and vertex-link discs when they occur, so it cannot
alone certify a compressing disc. A recognition integration must preserve
componentwise boundary essentiality, diagram-to-exterior provenance, and any
embedding or attachment data required for subsequent cuts. The existing
boundary-homology and component-coordinate observers remain relevant for
those tasks.
