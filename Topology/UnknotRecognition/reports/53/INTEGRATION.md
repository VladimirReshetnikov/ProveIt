# Integration notes

## Baseline and review boundary

The baseline is ProveIt commit
`7518823550fbc8c217bc8be0113fe52002e77465`, at
`Topology/UnknotRecognition/fast`.

The archive's `code/fast` is a complete runnable snapshot of the Python package
with a focused test/fixture selection. The integration patch adds files only.
Existing package initialization, recognizer defaults, legacy certificates and
aggregate APIs remain byte-identical to the pinned baseline. If the target
checkout has changed, compare the dependency hashes and review the private
geometry/orbit interfaces before applying the patch.

From the target repository root, inspect and check the patch with:

```bash
git apply --stat /path/to/integration.patch
git apply --check /path/to/integration.patch
```

After review, `git apply /path/to/integration.patch` installs the additions. The
article and archived results can be placed in the repository's chosen research
report directory; they are not embedded in the code patch. The bundle itself
makes no remote commit or publication.

## Added runtime modules

| Module under `fastunknot/` | Responsibility |
|---|---|
| `weighted_orbits.py` | Signed integer vector weights, compressed histograms, source-bound orbit-trace reuse |
| `weighted_orbit_verify.py` | Independent residue-anchor and derivative transport, checked against unweighted local rules |
| `normal_component_geometry.py` | Integral cell ownership, boundary tree-cotree cycles, independent binary basis check, full-coordinate weights |
| `normal_surface_components.py` | Component census in three query modes and exact essential-disc count |
| `normal_component_verify.py` | Source reconstruction and independent component-certificate interpretation |
| `normal_disk_kernel.py` | Vertex-link subtraction, quadrilateral gcd reduction, exact count rescaling and verifier |

The public entry points are imported from these modules rather than from the
unchanged package `__init__.py`.

The main baseline interfaces used directly are `integer_codec.py`,
`interval_orbits.py`, `interval_orbit_verify.py`, and
`normal_surface_geometry.py`. The full package snapshot is retained because
its initializer imports the existing recognizer infrastructure. Do not trim it
by examining only the six new modules' direct imports.

## Native API contract

```python
from fastunknot.normal_surface_components import normal_component_census
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.normal_disk_kernel import (
    normal_compressing_disk_count,
    verify_normal_disk_count_certificate,
)
```

`normal_component_census(triangulation, coordinates, mode='disk', ...)` accepts a
finite manifold triangulation in the maintained format and admissible standard
normal coordinates, with four triangle and three quadrilateral entries per
tetrahedron. Validation requires a compact connected orientable manifold with
exactly one torus boundary and sphere/disc vertex links.

| Mode | Weight dimension | What each histogram row records |
|---|---:|---|
| `disk` | 3 | Euler characteristic, two boundary parities, compressing-disc predicate, multiplicity |
| `summary` | 5 | The same plus normal polygon count and boundary intersection-point count |
| `coordinates` | 7t | The same plus the actual connected component's standard normal vector |

Boundary point count is not boundary-circle count. Histogram multiplicities are
binary integers. Different components with the same requested signature can share
a row. Full-coordinate mode gives actual component vectors, with equal vectors
grouped, and can supply a disc vector for a later geometric operation.

`normal_compressing_disk_count(...)` validates the original vector, removes its
vertex-link components, divides the remaining vector by quadrilateral gcd, and
counts essential discs on the resulting core. It returns the exact count in the
original vector. It deliberately does not return the original total component
count: multiplication can turn two copies of a one-sided surface into its
connected orientation double.

Both producers support `record_certificate=True`, `periodic_rule='fine_wilf'`
(or the maintained classical `'aht'` choice), `max_cycles`, and cancellation via
`check`. Exceeding an orbit allowance returns `INCONCLUSIVE`. A complete negative
answer means only that this supplied surface has no essential disc component.
Callbacks can cancel source validation, construction and replay; their exceptions
propagate.

The census can accept `orbit_certificate=...` to validate and reuse an existing
unweighted trace. This requires `max_cycles=None`, since no discovery runs.
The count-only wrapper does not expose an outer original-coordinate trace-reuse
argument: its source for the orbit query is the canonical core.

## Certificate schemas and trust

- `weighted-interval-orbits-v1`: canonical weights, universe, dimension,
  unweighted orbit proof, exact weighted histogram.
- `normal-component-census-v1`: original source fingerprint, mode, checked
  boundary basis, weighted proof, interpreted component summary.
- `normal-disc-count-v1`: original fingerprint, vertex-link multiplicities,
  quadrilateral divisor, core vector and certificate, exact final count.

Verifiers receive the source triangulation/vector independently of the certificate.
They revalidate the source and rebuild the required pairing/weight data. The
weighted checker does not discover an orbit order or call producer transport.
The normal layers share the finite input model and geometric weight construction;
this is why a separate external Regina oracle is included.

Python replay is executable evidence, not proof-assistant formalization. A valid
finite torus-boundary manifold is also not a certificate that it is the exterior
of a particular knot diagram. That source bridge and a complete normal-vector
producer remain separate recognition work. The two-weight ambient-homology
refinement proved in the article is a future variant, not an implemented mode.

## Tests and evidence

The new methods are in `tests/test_weighted_orbits.py` (13) and
`tests/test_normal_components.py` (17). Seven relevant existing test files bring
the portable selection to 103 methods; all passed with Regina available.
`test_normal_surface_certificate.py` imports `test_normal_surface_orbits` directly,
so use unittest discovery or include the tests directory on `PYTHONPATH`.

The four research drivers are portable when invoked through `reproduce.py`:

- `kernel_audit.py`: 10,000 literal interval cases and huge closed-form cases;
  also a controlled interval-only dimension benchmark.
- `checker_audit.py`: independent 2,500-case union-find audit, 366 deliberate
  mutations and producer-disabled replay.
- `normal_audit.py`: independent Regina corpus, all three query modes and
  normalized count certificates. Use the archived `--corpus` for repeatability.
- `normal_benchmark.py`: actual normal-vector query comparisons with full
  independent replay and identical A/A arms.

For a repository checkout, the selected tests can be run using ordinary unittest
discovery in a directory containing that selection. Full discovery of the
repository's existing test directory additionally runs unrelated application
coverage; that broader suite was not claimed as rerun for this archive.

## Suggested first integration

Expose the new source-bound query as an opt-in native operation. Preserve
`COMPLETE`/`INCONCLUSIVE` semantics and the exact distinction between a supplied
surface and an original knot. Retain the two aggregate-invariant counterexamples
as regression fixtures. Require a separately verified diagram-to-exterior bridge
before using a positive disc count as a knot verdict. A complete candidate search
or certified hierarchy needs its own complexity and completeness argument.
