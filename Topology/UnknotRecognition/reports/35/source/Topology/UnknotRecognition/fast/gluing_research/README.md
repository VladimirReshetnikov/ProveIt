# Checked full-boundary surface-cover assembly

`fastunknot.surface_gluing` extends the existing dihedral surface-cover kernel
with complete boundary gluing. It validates seam maps, retains original
patch/port/sheet coordinates, constructs a spanning-tree gauge, and classifies
the resulting cover without expanding sheets. The assembled base can be closed
or disconnected; each connected base has at most three component-family records.

This module operates on a supplied geometric presentation. It is not called
by `recognize`, does not extract normal surfaces, and does not certify an
embedding in a knot exterior. Its bit complexity is polynomial in the supplied
compressed description. General quasi-polynomial recognition remains open.

## Input schema

All indices are zero based. `sheets` is a positive integer or exact hexadecimal
string. Each patch uses the canonical bordered-surface schema from
`surface_cover`, omitting its own sheet count. Genus means handles when
orientable and crosscaps otherwise.

```json
{
  "sheets": 20,
  "pieces": [
    {
      "surface": {"orientable": true, "genus": 0, "boundary_components": 2},
      "monodromy": [{"sign": 1, "shift": 2}]
    }
  ],
  "seams": [
    {
      "left": [0, 0],
      "right": [0, 1],
      "direction": 1,
      "map": {"sign": -1, "shift": 0}
    }
  ]
}
```

Canonical boundary directions use local orientation frames transported along
fixed boundary whiskers. A seam's `direction` is the degree of the map between
these directed base circles. Its `map` transports the reference fibre from
`left` to `right`. The kernel checks

`A ∘ B_left = B_right^direction ∘ A`

as equality of actual sheet permutations, including one- and two-sheet
degeneracies. The fibre map's `sign` is independent of the seam's orientation
effect. Every boundary may occur once. A self-seam must use two different
boundaries. A seam identifies both complete base boundaries and all lifted
circles; partial intervals and selected lifted circles are outside this model.

The displayed input produces two degree-10 Klein bottles. Replacing only the
seam shift `0` by `1` produces one degree-20 torus. For every even `W=2m`,
the same change switches between two degree-`m` Klein bottles and one
degree-`2m` torus, while the local annulus cover remains unchanged. These are
abstract surface covers; no embedding of the Klein bottles in a knot exterior
is asserted.

## APIs and evidence

```python
from fastunknot.surface_gluing import GluedCoverIndex, verify_gauge_certificate

index = GluedCoverIndex(raw)
summary = index.summary
assert verify_gauge_certificate(raw, index.gauge_certificate)
component = index.component_key(piece=0, sheet=0)
circle = index.port_lift_key(piece=0, boundary=0, sheet=0)
image = index.transport_across_seam(seam=0, sheet=0)
signature = index.marked_signature(0, 0, marks=[(0, 0), (0, 2)])
point_image = index.transport_point((0, 0), (0, 2), (0, 4))
```

The summary retains normalized full input, root generators, orientation
characters, remaining peripherals, component topology and multiplicities,
and a transport-forest certificate. Summaries and certificates are defensive
copies. The verifier freshly validates the input and forest equations; it does
not trust serialized genus or component claims.

`port_lift_key` distinguishes remaining boundaries from internal seam circles.
Keys on opposite seam sides agree after the prescribed sheet transport.
`boundary_lift_key` rejects a consumed boundary. Keys retain original ports or
seam identifiers rather than merging merely homeomorphic objects.

Marked signatures classify ordered fibre points over this fixed sewn base.
They retain piece labels and the normalized model. Rooted cover maps require
anchors over the same piece basepoint and can then be evaluated anywhere in
the source component. A nonexistent map returns `None`; invalid points raise
`ValueError`.

`index.with_seams(additional)` produces a new fully checked index while retaining
original `(piece, sheet)` coordinates and leaving the earlier index intact.
It recomputes the assembly and has no incremental or amortized speed guarantee.
Cooperative cancellation propagates; interrupted work returns no partial
topology as a completed answer.

## Reproduction

From the `fast` directory:

```sh
python -B -m fastunknot.surface_gluing gluing_research/examples/klein_twenty.json
python -B -m fastunknot.surface_gluing gluing_research/examples/torus_twenty.json --port 0 0 0
python -B -m unittest tests.test_surface_gluing -v
python -B gluing_research/benchmark.py --output results/surface_gluing_local.json
```

The command accepts `--seconds` as a cooperative allowance. Large integers use
exact hexadecimal JSON without changing Python's decimal-conversion limit.

## Mathematical and validation scope

Let `s` count patch, generator, boundary and seam records, and let `B` bound
integer bit lengths and `log(s+2)`. Complete classification takes conservative
`O(s B^3)` bit time and `O(s B)` output bits. No loop depends on sheet count,
component multiplicity or the number of lifted circles. Prepared ordered
`q`-point queries take `O(q B^2)` work, plus the complete model-header size
when copied, compared or serialized. Full proofs are in `proof_notes.tex`.

The independent oracle constructs the graph on `(piece, sheet)` vertices,
propagates orientation parity, evaluates literal peripheral permutation
cycles, and sums patch Euler characteristics. Labelled-edge propagation checks
rooted cover maps directly. It imports no gauge, gcd classifier,
canonical-schema builder or marked-signature formulas.

The 14 focused tests pass: **1,547 expanded topology comparisons** and
**6,216 ordered marking comparisons**, plus binary tests through `W=2^24000`,
64-patch gauge chains, closed genus-two bases, projective-plane/sphere caps,
immutable seam continuation, alternative roots, corrupt certificates, invalid
seams, hexadecimal CLI transport and cancellation. The accompanying research
archive retains the focused run as `validation/gluing_focused.log`.

## Recorded measurements

`../results/surface_gluing_20261008.json` retains five shuffled measured rounds,
one excluded warmup, inputs or exact construction, execution orders, source
hashes, batch lengths, output sizes and A/A controls. Compressed timers include
all validation, assembly, classification and defensive summary creation.
Correctness checks and JSON serialization are outside timing. The compressed
microsecond cases use 100-query batches; the table reports median per-query
time. Expanded queries build the complete lifted graph once per sample.

| Cover | Sheets | Compressed (ms) | Explicit graph (ms) | Explicit / compressed |
|---|---:|---:|---:|---:|
| Two Klein bottles | 256 | 0.0926 | 0.453 | 4.9 |
| Two Klein bottles | 4,096 | 0.0818 | 8.952 | 109.5 |
| Two Klein bottles | 65,536 | 0.0862 | 291.679 | 3,383.7 |
| One torus | 65,536 | 0.1229 | 308.918 | 2,512.7 |
| Projective-plane/sphere cap | 16,384 | 0.0993 | 88.033 | 886.5 |
| Genus-two base | 16,384 | 0.1625 | 279.716 | 1,721.0 |
| Eight-patch closed chain | 4,096 | 0.3554 | 125.250 | 352.4 |

Identical compressed A/A control ratios range from **0.916 to 1.016**.
These ratios measure avoided explicit expansion, not superiority to another
compressed orbit algorithm and not a knot-recognition speedup.

For `W=2^16384` and 64 patches, full assembly plus summary takes 3.571 ms,
separate certificate replay 1.283 ms, and a prepared ordered 32-point query
0.518 ms per query. The serialized summary has 782,029 bytes including
normalized input and provenance; the full marked signature has 494,410 bytes.
Binary-scaling preparation A/A ratios range from 0.902 to 1.133, so small
constant-factor differences should not be overinterpreted.

Hierarchy integration still needs checked extraction of this model, support
for more general partial attachments, and bounds on the number and size of
successive repair states. Constantly many unmarked component families do not
bound the possible marked search states.
