# Integration notes

## Baseline and patch

This patch is based on ProveIt commit `bc5b913850f78155ccfddd808d4b11517dca252d`.

From a checkout of that commit:

```bash
git apply --check /absolute/path/to/integration/changes.patch
git apply /absolute/path/to/integration/changes.patch
cd Topology/UnknotRecognition/fast
python -B -m unittest discover -s tests -v
```

At a later commit, inspect conflicts and existing equivalents before applying. In particular, the worker communication repair may already have been integrated from the earlier incoming archive. The distribution's `--verify` command checks exact application against its included baseline without downloading the repository.

The article can be placed in the next appropriate report directory. Its relative `generated/` directory must travel with the TeX file. The archive does not choose a potentially conflicting report number.

## Primary splitting

```python
from fastunknot import Diagram, recognize
from fastunknot.scalar_split import fitting_khovanov_rank, fitting_khovanov_decide

diagram = Diagram.from_braid(2, [1, 1, 1])
verdict = recognize(diagram, backend="primary", seconds=10, max_objects=10000)
exact = fitting_khovanov_rank(diagram.pd, fitting_primary=True)
decision = fitting_khovanov_decide(diagram.pd, fitting_primary=True,
                                   seconds=10, max_objects=10000)
```

Run from `source/Topology/UnknotRecognition/fast` in the standalone package, or the corresponding directory in ProveIt:

```bash
python -m fastunknot recognize examples/trefoil.json --backend primary --seconds 10
python -m fastunknot khovanov examples/trefoil.json --primary
```

`recognize` can finish through an earlier valid certificate without invoking the selected Khovanov backend. Use the exact rank command or direct wrapper to exercise raw scanning. The exact `khovanov --primary` CLI is uncapped, consistent with the existing Fitting CLI. Use `recognize` or the Python API for an explicit object/time allowance.

Default behavior is unchanged. Primary splitting is opt-in and retains the existing 48-object, 1,024-variable, bounded-candidate policy unless the caller changes the corresponding scanner options. A failed polynomial search is not an indecomposability certificate. A global resource failure yields `UNKNOWN` in bounded recognition. Serialized recognition results continue to report `quasipolynomial_guarantee: false`.

Core additions and edits:

- `fastunknot/primary_split.py`: exact minimal-polynomial and Berlekamp algebra routines plus positive verifier.
- `fastunknot/scalar_split.py`: optional primary fallback, protected cache policy, metrics, exact and capped wrappers.
- `fastunknot/recognize.py`, `fastunknot/__main__.py`: public dispatch and compatibility checking.
- `primary_research/families.py`, `benchmark_primary_split.py`: reproducible algebraic fixtures and benchmark.
- `tests/test_primary_split.py`, `tests/test_primary_integration.py`: twelve kernel and five integration methods.

The accepted split checks matching/homological/quantum types, commutation with the whole differential, actual idempotence, invertible splitting bases, and every transformed cross term. A polynomial positive witness only needs a valid annihilator; it does not trust a claimed minimality or fixed-space dimension as a negative certificate.

## Surface-cover assembly

```python
from fastunknot.surface_gluing import GluedCoverIndex, verify_gauge_certificate

raw = {
    "sheets": 20,
    "pieces": [{
        "surface": {"orientable": True, "genus": 0, "boundary_components": 2},
        "monodromy": [{"sign": 1, "shift": 2}],
    }],
    "seams": [{
        "left": [0, 0], "right": [0, 1], "direction": 1,
        "map": {"sign": -1, "shift": 1},
    }],
}
index = GluedCoverIndex(raw)
summary = index.summary                  # One torus, covering degree 20.
component = index.component_key(0, 3)
seam_circle = index.port_lift_key(0, 0, 3)
```

Change the seam shift from 1 to 0 to obtain two Klein bottles of degree 10. These are abstract cover examples, without a claimed embedding of the nonorientable closed surfaces in a knot exterior.

```bash
python -m fastunknot.surface_gluing gluing_research/examples/torus_twenty.json
python -m fastunknot.surface_gluing gluing_research/examples/klein_twenty.json --port 0 0 3
```

The schema uses a common binary sheet set, canonical bordered surface pieces, derived peripheral words, complete unused boundary seams, and affine monodromy `x -> ±x+a`. Every seam checks `A B_left = B_right^direction A` as actual permutations, including `W=1,2`. It permits self-seams and closed sewn bases.

`GluedCoverIndex` retains the complete normalized presentation. Queries include component families and labels, seam and residual-boundary lifts, ordered marks, and based covering-isomorphism transport. `with_seams(additional, check=...)` returns an immutable extension; it rebuilds the complete index and makes no amortized-update claim. The summary is a defensive copy. The separate gauge verifier certifies forest transport, not a caller-supplied genus assertion.

`gluing_research/README.md` specifies the full schema and query contracts. The standalone geometry API is not on the knot-verdict path. No normal-cut extractor, arbitrary partial interval-pairing support, or embedded 3-manifold recognition certificate is supplied.

## Worker reliability

The patch also integrates the previously supplied threaded one-submit `communicate` repair and adds a narrow classification of invalid worker text bytes. Both streams are tested, the child is reaped, and caller cancellation exceptions remain visible. This preserves the documented failure-to-`INCONCLUSIVE` contract. Actual Regina tests were skipped because Regina was not installed; simulated worker transport and malformed-output cases were run.

## Subsequent optimization

The article proves that a complete parent scalar commutant basis spans each child corner by projection and restriction. A static implementation could avoid repeated child commutant solves. This proposal is **not implemented** in the delivered code or included in its timings. For an unbiased comparison, replay the same candidate sequence or use canonical commutant bases; the same high-level policy can produce different candidates if its input basis changes.
