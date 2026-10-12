# Data and certificate format

## Arithmetic and ownership

All family domains are half-open integer intervals `[lo, hi)` with `lo < hi`.
Only signed isometries `i -> slope*i + shift`, `slope in {-1,1}`, are used on
ranks. Integers are exact; booleans are rejected as numeric fields.

`atlas.dumps` emits integers of more than 256 bits as `{"$hex":"..."}`;
negative values have a leading minus sign. `atlas.loads` decodes that form.
Do not feed these dictionaries directly to an integer-consuming API. The
preceding Morse format uses its own `bigint_hex` tag; the demo retains a Morse
certificate as its original JSON string to avoid conflating the codecs.

## Atlas

An atlas has four fields:

```
polytopes: [{name, vertices}]
families: [{name, poly, lo, hi}]
charts: [{upper, face, lo, hi, lower, slope, shift, vertex_map}]
marks: [{label, family, lo, hi}]
```

Prototypes have exact integer coordinates, are full-dimensional in their own
coordinate space, and have dimension at most three. Their complete convex
face lattice is reconstructed from supporting planes. Redundant/non-extreme
input vertices are rejected. A face is a bit mask of local prototype vertices.

A chart identifies a *particular proper local face occurrence* of an upper cell
with a whole lower cell. `vertex_map` lists target vertex indices in the order
of the sorted source-face vertices. It must be a face-lattice isomorphism.
Chart domains partition the entire upper family for each proper face; all
nested-face compositions must equal the direct charts. This enforces coherent
quotient attaching maps without requiring the original cells to be regular.

Each marked label describes a downward-closed union of complete cells. Several
labels may overlap. Intervals within one label/family must not overlap.
Marks are not arbitrary curves and do not by themselves carry knot-exterior
or boundary-pattern provenance.

## Flag certificate

```
{
  schema: "affine-flag-regularization-v1",
  source_sha256: "...",
  result: <atlas>,
  carriers: [{output, source, flag}]
}
```

`flag` is a strictly nested chain of nonempty local faces ending at the whole
prototype of `source`. Its length minus one is the output cell dimension.
The output family has precisely its source family's rank interval. Carrier
records must be unique and exhaustive. A count recurrence in the checker
certifies exhaustiveness; the checker does not enumerate the producer's flags.

The source hash detects mismatched inputs. It is **not** evidence that an atlas
comes from an external manifold. The independent checker validates the source,
all flag maps, the output incidence structure and every marked subcomplex.
Semantically equivalent subdivisions of chart domains may replay successfully;
certificates need not use byte-identical partitions to the producer.

## Examples and Morse bridge

`source-bound-flag-example-v1` envelopes contain `source_specification`,
`source_atlas`, `certificate`, its source hash, inventory and mode parameters.
The publication checker reconstructs the named controlled source independently
of the retained atlas and replays the certificate. The solid-torus envelope
also records its original zero-cut triangulation and literal comparison.

`packet_from_flags` translates regular codimension-one faces into the existing
`ranked-morse-v1` cover format. No face-occurrence summation, coefficient
cancellation or vertex-set deduplication is permitted. The supplied convex
cone examples attach an explicit matching with fixed integer ranks, checked
by the actual preceding arithmetic implementation.
