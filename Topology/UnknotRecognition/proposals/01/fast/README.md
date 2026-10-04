# fastunknot 0.2.0

Exact, dependency-free unknot recognition. General worst case: `2^O(n)`.
A small scanning boundary alone does **not** bound the number of homological
objects: an iterated trefoil sum can have boundary width 4 and rank `3**k`.
The new factorization path represents the product compactly instead.

See `../README.md` for timings, reproducibility, and the technical report.

## Library API

```python
from fastunknot import Diagram, recognize, khovanov_rank, verify_rejection

knot = Diagram.from_braid(2, [1, 1, 1])
result = recognize(knot, seconds=30, max_objects=200_000)
print(result.status, result.method)
assert verify_rejection(knot, result)

# Full unreduced/reduced total F2 ranks, with raw cube homological degrees.
# Does not compute integral torsion or a quantum bigrading.
rank = khovanov_rank(knot.pd, factor_connected=True, pivot="markowitz")
assert rank["reduced_rank"] == 3
```

`Diagram.from_pd(rows)` validates one component, edge incidences, and the sphere
rotation system, and compacts the edge labels. A row `(a,b,c,d)` is cyclic at a
crossing, with `(a,c)` under and `(b,d)` over. The empty PD represents a single
crossing-free unknot. Multi-component and virtual diagrams are rejected.

`Diagram.from_json(value)` accepts the original formats:

```json
{"braid": {"strands": 3, "word": [1, -2, 1, -2]}}
```

or `{"pd": [[...], ...]}`, a raw PD array, `{"rows": [[c1,c2], ...]}`, or
`{"x": [...], "o": [...]}`. Grid coordinates are zero-based. Runtime arithmetic
is exact: integers, F2 coefficient sets, or the fixed prime field 1000000007.

## Recognition options

```python
recognize(diagram, *,
    use_reduction=True, use_descending=True,
    use_alexander=True, use_modular=True, use_jones=True,
    factor_connected=True, max_jones_states=4096,
    max_objects=None, seconds=None,
    check_d_squared=False, pivot="markowitz")
```

`Result.status` is `UNKNOT`, `KNOTTED`, or `UNKNOWN`; `Result.is_unknot` is
`True`, `False`, or `None`, respectively. Resource-limit results include the
phase and reason. `Result.to_json()` returns a serializable dictionary.

Only modular rejection results are supported by `verify_rejection`. Its trust
base includes PD validation, Reidemeister legality, and the recomputation code;
it is not a formally verified or separately implemented proof kernel.

## Full Khovanov API

```python
khovanov_rank(pd, *, order=None, max_objects=None, seconds=None,
             check_d_squared=False, factor_connected=True, pivot="markowitz")
```

The returned `by_degree` is an unreduced rank histogram in **unshifted cube
degree**, not normalized oriented homological grading. Degree shifts can change
under R1/R2 moves, so compare total ranks when simplifying. An explicit scan
`order` must be a complete permutation and disables factoring. This is useful
for exact ablations. The public rank API now validates its PD input too.

Connected-sum cuts are diagrammatic, exact, and conservative. They are not a
prime-decomposition algorithm. Factorization preserves the degree histogram;
`stats` reports actual work and peak objects on individual factors. The reported
order is a concatenation of factor orders mapped to original crossings, not a
claim that an unfactored scan used that order.

`max_objects` limits pre-cancellation expansions of each individual factor;
it is not a byte-level RAM cap or a cap on the output rank integer.
`check_d_squared=True` adds potentially expensive algebra checks after each
crossing. It is intended for testing rather than performance measurement.

## Other functions and CLI

`fastunknot.jones.jones_evaluations(diagram)` returns two normalized Jones
specializations at A=2 and A=3 modulo the fixed prime, plus raw brackets, writhe,
order, and frontier statistics. It does not return the entire Jones polynomial.
A non-1 value proves knottedness; two 1s never prove unknottedness.

`fastunknot.modular.alexander_witness(diagram)` returns an exact one-sided
nonunit minor witness or `None`. The complete symbolic polynomial API is still
`fastunknot.alexander_polynomial(diagram)`.

`fastunknot.scan.clear_caches()` releases shared caches between experiments.
Cache entry counts are bounded, not total bytes. Cached morphisms are immutable;
internal cached geometry should be treated as read-only.

`python -m fastunknot --help` lists commands. There is no runtime network access
or optional solver requirement. On Windows the same commands work in PowerShell.

## Compatibility notes

Default method names can now be `alexander-modular-evaluation` and
`jones-modular-evaluation`. `--no-alexander` does not disable Jones: use
`--no-alexander --no-jones` to disable both families of rejection filters.
`Diagram.signs()` retains the original **local Fox signs**; `Diagram.writhe()`
now correctly uses both oriented branches. For this PD/bracket convention,
a positive braid generator has writhe -1. This is a convention, not a change to
the input knot type; the normalized bracket remains invariant.

`python -m unittest discover -s tests -v` works from this directory when it is
kept inside the supplied archive, because some differential tests import the
sibling unchanged baseline and independent test oracles.
