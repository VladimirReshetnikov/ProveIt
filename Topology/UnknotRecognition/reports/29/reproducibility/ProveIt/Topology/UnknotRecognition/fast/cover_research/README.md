# Binary surface covers and ordered marked points

`fastunknot.surface_cover` maintains report 24's dihedral surface-cover
classifier and adds exact comparison of components with ordered fibre points.
The delivered report stays unchanged in `../../reports/24/dihedral_covers`.
This is a geometric kernel for a supplied covering presentation. The knot
recognizer does not call it: extracting and checking such a presentation from
a knot exterior, preserving full attaching maps, and bounding hierarchy search
remain open integration obligations.

The input is a connected compact surface with nonempty boundary and a signed
affine monodromy map `x -> sign*x + shift (mod sheets)` for each canonical free
generator. `surface.orientable` is boolean; `genus` means handles or crosscaps,
and `boundary_components` is positive. The rank is `2*genus + boundaries - 1`
when orientable, and `genus + boundaries - 1` otherwise. The disk has rank zero.
Boundary words and orientation characters are constructed from this schema.
Closed bases and arbitrary supplied peripheral systems are outside the API.

```python
from fastunknot.surface_cover import CoverIndex

cover = CoverIndex({
    "surface": {"orientable": True, "genus": 0, "boundary_components": 3},
    "sheets": 12,
    "monodromy": [{"sign": 1, "shift": 4}, {"sign": -1, "shift": 0}],
})
summary = cover.summary  # Defensive copy, at most three component records.
assert summary["component_count"] == 3
assert summary["cover_isomorphism_type_count"] == 2
assert cover.marked_signature(0, [0, 4]) == cover.marked_signature(2, [6, 10])
assert cover.transport_sheet(0, 6, 4) == 10
boundary = cover.boundary_lift_key(0, 4)
```

The first `marked_signature` argument selects a component; it is not an extra
mark. Mark order matters and repeated points are allowed. Equal signatures
within a normalized input mean an isomorphism over the fixed base that respects
every ordered point. The signature includes the full normalized input, so it
does not silently compare different surface presentations. No marks gives the
unmarked cover type. `transport_sheet(source_anchor, target_anchor, sheet)`
evaluates the unique equivariant map with that root image, or returns `None`
when such a map does not exist. Invalid sheets and points outside the selected
component raise `ValueError`.

Raw `classify_cover`, `component_key`, and `boundary_lift_key` functions remain
available. The latter two require an actual classifier result. `CoverIndex`
constructs that result itself and retains a private copy; it does not accept a
serialized summary as a certificate. Optional `check` callbacks propagate
cancellation through preparation and queries. Their limits are cooperative;
individual integer operations and serialization are not hard-interruptible.

Every integer field accepts a literal integer or signed hexadecimal string;
booleans and decimal strings are rejected as integer fields. CLI sheet arguments
also accept decimal text. Large output integers use the shared exact hexadecimal
transport without changing Python's process-wide decimal conversion limit.

From the `fast` directory:

```sh
python -B -m fastunknot.surface_cover ../reports/24/dihedral_covers/examples/three_types.json
python -B -m fastunknot.surface_cover cover.json --component 0 --mark 0 --mark 4 --seconds 1
python -B -m unittest discover -s tests -p 'test_surface_cover*.py'
python -B cover_research/audit_markings.py --output ../synthesis/data/surface-cover-marked-local.json
python -B cover_research/benchmark.py --output results/surface_cover_local.json
```

The independent marking audit enumerates all equivariant fibre bijections for
every two-generator affine action through six sheets. It performs 196,712 marked
comparisons, 1,061 unmarked comparisons, 9,100 rooted comparisons and 38,746
transport checks over 364 presentations. The archive-derived suite separately
repeats 13,846 comparisons against lifted-spine graph search, orientation
propagation and boundary permutation cycles. Production tests also exercise
24,000-bit sheet counts, transport, input binding, invalid marks, defensive
copies, cancellation and the CLI.

The benchmark measures complete cover topology against explicit sheet expansion,
plus prepared marked queries with `W = 2^32, 2^1024, 2^16384`. It records seven
shuffled paired warm rounds, unchanged A/A controls, batch sizes, source hashes
and raw times. Expanded topology is an independent oracle, not an alternative
compressed algorithm. These measurements do not measure knot recognition or
compare against Agol–Hass–Thurston. The maintained proofs and measurements are
in `../../synthesis/surface_covers.tex`.

The classifier uses polynomial bit complexity and at most three unmarked
families. Ordered markings can have exponentially many equivalence types in the
bit length of the sheet count: a connected cyclic annulus cover with marks
`(0, j)` has one distinct type for each `j`. The new polynomial comparison
interface therefore does not by itself bound a hierarchy's number of states.
