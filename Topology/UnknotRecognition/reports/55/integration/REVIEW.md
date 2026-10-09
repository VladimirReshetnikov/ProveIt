# Native integration review — execution pending

The proposal adds a witness-extraction interface. It does not replace the orbit
scheduler, weighted histogram engine, geometry validator, or recognizer dispatch.

## Reviewed imports

The pinned revision is `b365341b1939c69a26b31bb5d05a097d4572692c`.
`normal_surface_geometry` supplies `_prepare`, `_coordinates`, `_fingerprint` and
`NormalOrbitError`. `normal_component_geometry` supplies `component_weight_system`,
`_edge_offsets`, and `disk_corner_intervals`. `normal_surface_components` supplies
`normal_component_census`. `normal_component_verify` supplies
`verify_normal_component_certificate`. `integer_codec` supplies encoded-integer
and JSON-safe utilities. These underscored native interfaces are not stability
promises; recheck them if integrating at another revision.

## Install without modifying dispatch

From a checkout of this delivery, set paths to this package and the native source:

```sh
export PYTHONPATH="$PWD/src:$PWD/integration:/path/to/ProveIt/Topology/UnknotRecognition/fast"
python -c 'from native_selective_disk import selective_normal_disk'
```

The native modules are imported lazily. The standalone package is installable
with `pip install .`, but using PYTHONPATH avoids installation entirely.

```python
from native_selective_disk import selective_normal_disk
result = selective_normal_disk(triangulation, coordinates,
                               max_cycles=None, max_nodes=2_000_000)
```

Status meanings:

- `COMPLETE`: one independently replayed normal-disc witness in the supplied
  validated manifold. Not a knot verdict.
- `NO_DISC_IN_SUPPLIED_VECTOR`: native three-weight negative census, independently
  replayed. Not a complete search or a knottedness verdict.
- `INCONCLUSIVE`: an allowance was exhausted; no proposed witness is published.

Cancellation exceptions propagate. Cycle budgets cover both native queries;
compilation has a distinct circuit-node allowance. These are not process-memory
or hostile-input containment limits.

## Native audit to run

Supply a JSON list of entries with `name`, `triangulation`, and `coordinates`, in
the exact formats accepted by the maintained native census.

```sh
python integration/audit_native.py \
  --fast /path/to/ProveIt/Topology/UnknotRecognition/fast \
  --fixtures native_cases.json \
  --output results/native_audit.json
```

The runner checks a selected positive vector against the existing full-coordinate
census, independently verifies its terminal certificate, and records native
module and fixture hashes. It does not currently implement a statistical native
benchmark, mutation corpus, or full recognizer regression test.

Promotion must additionally include the maintained test suite, source mutation
rejection, tests with compiler functions disabled during positive replay, enormous
coordinates, one-sided components, cancellation in every stage, and both positive
and negative complete-query benchmarks. The delivered `results/STATUS.json`
explicitly records these native tasks as **not run**.

## Certificate semantics

The positive certificate is `selective-normal-disc-v1`, containing the original
fingerprint, the proposed coordinates `y`, and a native `normal-component-census-v1`
certificate for `y`. The independent positive verifier does not import or call the
compiler. It reads only the native verified summary, requiring one component and
one compressing-disc component, and checks `y <= x` after normal validation.

It proves a disc, not independently that `y` is a component of `x`. The stronger
component theorem relies on the correct source geometry and compiler theorem.
A hierarchy consumer requiring actual component provenance should retain and
verify the corresponding source trace/ownership binding as a separate obligation.
