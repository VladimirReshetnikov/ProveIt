# Integrating boundary transport

The implementation lives in `fast/fastunknot/boundary_transport.py` and
depends only on the existing `surface_cover` and `integer_codec` modules.
It adds no third-party dependency and is separate from knot recognition.

## Prepared index and accepted model

```python
from fastunknot.boundary_transport import BoundaryTransportIndex

cover = {
    "surface": {
        "orientable": True,
        "genus": 0,
        "boundary_components": 4,
    },
    "sheets": 360,
    "monodromy": [
        {"sign": 1, "shift": 1},
        {"sign": 1, "shift": 12},
        {"sign": 1, "shift": 18},
    ],
}
index = BoundaryTransportIndex(cover)
```

The input is the existing canonical bordered-surface covering model. The
number and order of generator maps must match that surface schema. Boundary
words are constructed by the validator; they are not arbitrary user-supplied
words. For a nonorientable base, `genus` means crosscap number.

The inherited index preparation validates and normalizes the presentation.
Passing a previously serialized classification does not substitute for that
validation. All subsequent comparisons refer to this one fixed base
presentation, its generator ordering, and its chosen peripheral paths.

## All maps satisfying boundary and point constraints

The actual method signature is:

```python
index.transports(
    source_component,
    target_component,
    *,
    point_pairs=(),
    boundary_pairs=(),
)
```

The component arguments are sheet selectors, **not extra marked points**.
`point_pairs` contains `(source_sheet, target_sheet)` pairs.
`boundary_pairs` contains `(base_boundary_index, source_sheet, target_sheet)`
triples. Boundary indices are zero-based. A boundary triple requires the
whole peripheral orbit of its source sheet to map to the whole peripheral
orbit of its target sheet. It does not require those two sheets themselves
to map to one another. The lists are ordered, may contain repetitions, and
must be finite lists or tuples.

For the prepared example:

```python
maps = index.transports(
    0, 0,
    boundary_pairs=[(1, 0, 5), (2, 0, 11)],
)
assert maps["source_root"] == 0
assert maps["isomorphism_count"] == 10
assert maps["root_progressions"] == [
    {"first": 29, "step": 36, "count": 10},
]

root = maps["source_root"]
image = maps["witness_target_anchor"]
assert index.transport_sheet(root, image, 12) == 41
```

Each progression represents `first + j*step` for `0 <= j < count` as an
image of `source_root`. There are at most two disjoint progressions, sorted
by `first`; an image determines one equivariant covering isomorphism. Use
`transport_sheet` to evaluate that map on requested sheets. The family can
be enormous, so callers should retain the progressions rather than expand
their members.

A point constraint can select a single map from the family:

```python
pinned = index.transports(
    0, 0,
    point_pairs=[(7, 36)],
    boundary_pairs=[(1, 0, 5), (2, 0, 11)],
)
assert pinned["isomorphism_count"] == 1
assert pinned["witness_target_anchor"] == 29
```

No compatible map is represented by an empty progression list,
`isomorphism_count == 0`, and `witness_target_anchor is None`.
Malformed inputs or marks outside their selected components raise
`ValueError`. Neither outcome is a knot verdict.

## Canonical keys for pure translation presentations

The actual method signature is:

```python
index.cyclic_marked_signature(
    component_sheet,
    *,
    point_marks=(),
    boundary_marks=(),
)
```

`point_marks` lists sheets. `boundary_marks` lists
`(base_boundary_index, sheet)` pairs. Point slots are processed in their
order, followed by boundary slots in their order. The normalized base model,
slot schema, and canonical tuple form the complete hashable key.

```python
left = index.cyclic_marked_signature(
    0, boundary_marks=[(1, 0), (2, 0)],
)
right = index.cyclic_marked_signature(
    0, boundary_marks=[(1, 29), (2, 29)],
)
assert left["signature"] == right["signature"]
assert left["marking_type_count"] == 6
assert left["isomorphism_count_to_canonical"] == 10
```

The result also includes `source_root`, `canonical_root_image`,
`canonical_component` (the residue-zero component), and `phase_modulus`.
The root image supplies a witness transport to the canonical form. The
method rejects any presentation containing a negative affine sign;
`transports` remains available for general dihedral presentations.

For mark periods `q_i | m`, the exact type count is
`product(q_i) / lcm(q_i)`. That integer may be larger than the root-map
count and may require `O(kB)` bits. The conservative costs are
`O((k+1)B^3)` for a transport query and
`O((k+1)B^3 + k^2 B^2)` for the canonical key together with its expanded
binary type-count integer.

## Mathematical boundaries of this API

- Isomorphisms are **over the identity of the fixed base surface**. An
  isomorphism after changing the base presentation, generator system, or
  boundary labels is a different problem.
- Whole-circle markings are **unparameterized**. Arbitrary attaching maps,
  twists, and their phases are not represented merely by a boundary triple.
- The solver returns **all covering isomorphisms**. It does not impose a
  chosen orientation on covering components or a direction on interval
  fibres. Such constraints need their own conventions and checks, especially
  for orientable covers of nonorientable bases.
- The validated cover is supplied to the kernel. Extracting it from a
  normal surface or parallelity bundle, checking its ambient embedding, and
  transporting a complete three-dimensional gluing remain separate tasks.
- A canonical key certifies this precise equivalence relation. It is not a
  complete key for an ambient hierarchy state with extra attachment data.

## Integers, cancellation, and command line

Use exact integers or the repository's signed hexadecimal integer strings.
Booleans, floating values, and decimal strings are not accepted as integer
fields. `fastunknot.integer_codec.json_safe` prepares large integers for JSON
without changing Python's process-global decimal conversion limit.

`BoundaryTransportIndex(cover, check=callback)` accepts a cooperative
cancellation callback. Exceptions propagate; cancellation never becomes an
empty map family. Individual integer operations and bulk serialization are
not hard-interruptible.

From the `fast` directory:

```bash
python -m fastunknot.boundary_transport /path/to/example-query.json
python -m fastunknot.boundary_transport /path/to/example-query.json --seconds 2
python -m unittest tests.test_boundary_transport
```

The command-line input has exactly two objects, `cover` and `query`.
The supplied `example-query.json` is the ten-map example above. Independent
oracle and benchmark commands are documented in `RESULTS.md`.
