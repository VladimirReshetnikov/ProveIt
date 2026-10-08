# Integration and usage

This continuation targets ProveIt commit
`9cec5275f2d2113d0a784cedf156460829b61489`.
The production default remains `reduction="standard"`.
The new reducers are exact experimental options. The ordinary sparse scanner
is faster on the actual diagrams measured in this report.

Keep `fast/` and `reference/` as sibling directories when running the supplied
tests and historical benchmarks. The frozen reference modules are deliberately
retained: several checks compare the new implementation with them. The
standalone `dihedral_covers/` directory has a separate input contract.

## Recognition and raw Khovanov rank

Run these commands inside `fast/`:

```sh
python -m fastunknot khovanov examples/conway.json \
  --reduction corridor --check-d2

python -m fastunknot recognize examples/conway.json \
  --reduction corridor-adaptive --seconds 30 --max-objects 50000
```

`corridor` transfers the full minimal differential at each reduction stage.
`corridor-adaptive` first permits `max(256, 4*N)` ordinary Schur-update pairs
for the stage, retaining completed pivots before switching if necessary.
This allowance is a heuristic, not a runtime guarantee.

The older `adaptive` mode only attempts a zero-differential residue shortcut
and resumes ordinary reduction when that shortcut fails. The new adaptive
mode can return a nonzero radical differential.

Normal recognition can finish in a braid, Seifert, polynomial, or other
earlier certificate stage. To exercise the raw scanner directly:

```python
from fastunknot import Diagram, khovanov_rank

diagram = Diagram.from_braid(3, [1, -2] * 4)
result = khovanov_rank(
    diagram.pd,
    reduction="corridor-adaptive",
    max_objects=50000,
    seconds=30,
    check_d_squared=True,
)
print(result["rank"], result["by_degree"])
```

The returned rank and degree conventions are unchanged. The reduction name
and work counters appear in the result. The `--no-reduction` switch still
disables Reidemeister preprocessing; it is distinct from `--reduction`.

## Compatibility

The public corridor modes require:

- The standard scanner backend.
- Minimum-fill pivots and bit-packed algebra.
- `self_inverse=True` in the raw API.
- `race=1`.
- `window_radius=None` in recognition.

They cannot be combined with the shared, saturated, Euler, or twist
backends. The separate `window` command retains its previous reduction
choices. The standard, component, and forced component-dense coefficient
engines remain supported, as does the existing `tail` contraction option.
Invalid combinations are rejected.

## Sparse scalar setup and direction experiments

Additional controls are available on the direct scanner and transfer kernel:

```python
from time import monotonic
from fastunknot.corridor import CorridorScan
from fastunknot.ordering import best_scan_order

scan = CorridorScan(
    mode="auto",
    prune=True,
    direction_policy="ports",
    scalar_engine="components",
    max_objects=50000,
    deadline=monotonic() + 30,
)
for index in best_scan_order(diagram.pd):
    scan.add_crossing(diagram.pd[index])
print(scan.total_rank())
```

This example uses the validated nonempty diagram created above. Prefer
`khovanov_rank` for ordinary calls, including the established zero-crossing
convention and public dispatch.

`mode` is `forward`, `reverse`, or `auto`. The `reach` direction policy uses
packed endpoint sets and the finer propagation bound. The `ports` policy uses
Boolean reachability and counts input/output ports. The scalar engine is
`global` or `components`. The latter returns sparse scalar index columns and
handles isolated objects and scalar identity pairs directly.

Public `corridor` and `corridor-adaptive` use `auto`, pruning, `reach`, and
`global`. There is no public `corridor-compressed` reduction name in this
release. The direct controls also work with `AdaptiveCorridorScan`.

`corridor_transfer(scan, ...)` requires a valid homogeneous complex and
returns a complete replacement plus scalar contraction, component details,
and counters. It does not replace the input object or differential arrays;
coefficient caches may be populated.

## Resources and diagnostics

The object ceiling checks the predicted expansion count before allocating
the new objects. It does not bound total Python memory or every auxiliary
matrix. Deadlines are cooperative.

The raw `khovanov_rank` API raises `ScanLimit` or `MemoryError` on resource
failure. Recognition returns `UNKNOWN` with resource evidence. Exhaustion
never becomes an unknot or knotted verdict.

`GradedScan.check_grading()` checks every stored monomial's grading.
`check_d_squared=True` checks the differential square after each crossing.
`ranks_by_bidegree()` returns raw live-object multiplicities; these are
homology dimensions only when the differential is known to vanish.

Relevant counters include graph and retained sizes, direction choices,
structural propagation bounds, actual propagations, radical-edge
propagations, compositions, and adaptive switches. Elapsed-time measurements
include scalar setup and graph setup. Radical-edge counts measure the
corresponding propagation work.

## Verification and evidence

Inside `fast/`:

```sh
python -m unittest discover -s tests -v
python audit_graded_support.py --output results/graded_support_local.json
python audit_scalar_representation.py --output results/scalar_representation_local.json
```

The released scanner suite passed 268 tests. The supplied final manifest and
logs identify the tested snapshot. The inexpensive support audit reports
72 actual diagrams, 639 stages, and zero added support-only shortcuts.
The representation audit compares all scalar contraction maps exactly and
checks the quadratic packed-bit versus linear sparse-index formulas.

The primary recorded benchmarks are:

- `fast/results/corridor_benchmark_20261008.json`
- `fast/results/compressed_corridor_20261008.json`

The reproduction wrapper restores the frozen corridor in a temporary copy
when replaying the historical nine-arm benchmark. Use that wrapper for a
hash-matched historical run; the separate compressed experiment explicitly
loads the frozen baseline. The result files contain all cases, crossing
orders, raw samples, repetition counts, counters, and source hashes.

The strict shared-suffix family demonstrates 130,305 versus 765 radical-edge
attempts at size 255 and an approximately 28.4-fold measured gain over the
inherited forward transfer. Ordinary sparse cancellation remains faster on
that family. Neither the general corridor strategy nor its sparse-setup
refinement supplies a reliable practical improvement on the actual diagram
cases measured here. These results do not establish unrestricted
quasi-polynomial unknot recognition.

## Dihedral surface covers

From the package root:

```sh
python dihedral_covers/dihedral_cover.py \
  dihedral_covers/examples/three_types.json
```

Inside `dihedral_covers/`, the Python API provides `classify_cover`,
`component_key`, and `boundary_lift_key`; its README gives the canonical
generator order and complete JSON schema.

The classifier returns at most three component-family records, with
multiplicities, topology, boundary covering degrees, and covering-isomorphism
type identifiers. Marked queries retain individual component and boundary
labels without expanding the sheet set. The interval-bundle field refers
to the canonical bundle with orientable total space.

This kernel classifies an explicitly supplied abstract bordered-surface
cover. It does not extract a cover presentation from a normal surface,
certify its embedding in a knot exterior, or recover unspecified external
attachments. Those are separate integration obligations.
