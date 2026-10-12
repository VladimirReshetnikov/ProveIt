# Compressed Saturated Interval Bundles and Exact Full-Row Cancellation

Research continuation for **ProveIt / Topology / UnknotRecognition**, dated 12 October 2026.

The article is `article/saturated_bundle_cancellation.pdf`. Its complete LaTeX sources, figure sources, implementation, independent verifiers, tests, saved certificates, and measurements are included.

## Main results

- A geometric residual-incidence theorem for saturated bordered interval bundles: each residual two-handle uses the unsigned sum of its authenticated annulus incidences on the original core; every own private cocore is met twice.
- Binary private-handle counts and a connector-forest correction permit a complete unmarked handlebody census without expanding the base genus.
- Exact full-row column peeling, a canonical stopping-set obstruction, and an independent timestamp verifier. The matching theorem is a consequence of existing report 56; the old minimum-fill producer was already complete for the full-row verdict.
- An optional early core filter justified by row-subset monotonicity.
- A proved, conditional observer-family incidence bound, and an additive ordinary-compression repair bound for authenticated ambient surface blocks. These two extensions are mathematical results; their missing geometric transport inputs are not implemented.

The new native consumer certifies **85 of 106 supplied normal cuts**, compared with **78** at the inspected baseline. All old successes remain valid. All 96 compiled conclusions independently replay; all 78 positive cases small enough for the literal Regina oracle agree with it. Seven positive binary cases exceed the explicit expansion cap. Twenty-one cases remain inconclusive. This package does **not** claim a global quasi-polynomial unknot-recognition algorithm.

## Reproduce

Use Python 3.12 or a compatible modern Python. The extension and its tests need only the standard library. The recorded environment used Python 3.12.14.

```bash
PYTHONPATH=code:runtime python3 -B -m unittest discover -s tests -v
PYTHONPATH=code:runtime python3 -B experiments/replay_saved.py
```

The first command includes a full 106-case precheck comparison and may take around a minute or more, depending on the machine. The recorded combined run passed **37 test methods**. The pinned repository's separate full regression run passed **1,663 tests**; its original directory layout is required to reproduce that larger run.

To rerun the literal cut audit, install Regina separately (the recorded version was 7.4):

```bash
PYTHONPATH=code:runtime python3 -B experiments/native_audit.py
```

To measure performance, stop other test and experiment processes, then run the following commands sequentially:

```bash
python3 -B experiments/benchmark_column_peeling.py
PYTHONPATH=code:runtime python3 -B experiments/benchmark_native.py
```

The scripts preserve alternating-order samples and A/A controls. The kernel measurements show quadratic-to-linear incidence work. Complete common-success calls are mostly unchanged and include small regressions; the optional early refusal path avoids actual boundary queries on five corpus cases. See the article and raw data for exact task definitions.

Build the article with a standard LaTeX installation:

```bash
python3 -B build_article.py
```

The PNG and SVG figure are supplied. To regenerate them, additionally install Matplotlib and run `python3 -B experiments/generate_figures.py`.

## Use the new operator

With `code` and `runtime` on `PYTHONPATH`:

```python
from normal_cut_saturation import normal_cut_saturation
from normal_cut_saturation_verify import verify_normal_cut_saturation

answer = normal_cut_saturation(
    triangulation, normal_coordinates,
    record_certificate=True,
    precheck_core=True,  # optional; defaults to False
)
if "certificate" in answer:
    assert verify_normal_cut_saturation(
        triangulation, normal_coordinates, answer["certificate"]
    )
```

`COMPLETE` means an exact handlebody census of the supplied cut. A verified `INCONCLUSIVE` certificate can establish a raw stopping-set obstruction, which is not a negative topological or knot verdict. Resource exhaustion and unsupported three-handles or closed bases can return without a certificate.

## Source and integration

Inspected repository commit: `704600626606a9097cfd89d4e3d2bbc63c8dd1cb`.
Original inherited corpus revision: `d2c5e1707fe783bbed06743ac732d70d83e6f27b`.

The files under `runtime/` and the baseline comparator are unchanged excerpts of the inspected repository. The six new modules live under `code/`. `integration/additive_extension.patch` adds namespaced versions of them to the repo without changing default consumers. See `INTEGRATION.md` for application and validation, and `CLAIMS.md` for the exact claim boundaries.

The principal evidence is in `data/native_audit.json`, `data/core_precheck_audit.json`, `data/native_benchmark.json`, `results/column_peeling_validation.json`, and `results/column_peeling_benchmark.json`. All seven new successes have saved certificates under `data/certificates/`, alongside legacy, binary, and obstruction controls.
