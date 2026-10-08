# Boundary transport: results and reproduction

This contribution extends the repository's checked dihedral surface-cover
kernel from ordered fibre points to ordered **whole lifted boundary circles**.
It computes every compatible covering isomorphism as at most two binary
arithmetic progressions of root images. For pure translation covers, it also
computes a canonical marked key, a witness map, and the exact marking-type count.

The inspected repository revision was
`8a95834940cf77cdab1b39571ffc102ca8b6bede`. The new files are
`fastunknot/boundary_transport.py` and `tests/test_boundary_transport.py` in the
existing `fast` tree. No recognition path or existing core file was changed.
Complete proofs are in manuscript Section 6, “Transporting marked boundary lifts.”

## Mathematical guarantees

With `k` constraints and `B`-bit integers, a prepared transport query costs
`O((k+1) B^3)` bit operations conservatively and returns `O(B)` bits. The
implementation retains `O((k+1) B)` bits of query data. No loop depends on the
sheet count, number of components, or number of returned maps.

For connected covers with marked boundary-lift degrees `e_i`, a nonempty
family of compatible maps has cyclic ambiguity of order dividing `gcd(e_i)`.
A point correspondence leaves at most one map.

For cyclic components of degree `m`, let `q_i | m` be the periods of the
mark slots. The exact number of marking types is
`product(q_i) / lcm(q_i)`, and every marking has `m / lcm(q_i)` automorphisms.
Canonical keys cost `O((k+1) B^3)` bit work. Returning the potentially
`kB`-bit exact type count adds the conservative product cost `O(k^2 B^2)`.
Thus the full signature-and-count method costs
`O((k+1) B^3 + k^2 B^2)`.

For `k >= 1` whole-circle slots on a connected cyclic surface cover `C`, the
number of types is at most `max(2, -chi(C))^(k-1)`. Polynomial negative Euler
complexity and logarithmically many attachments therefore give a
quasi-polynomial number of these **local normalized marking states**. Point
phases and parametrized gluing maps are outside this bound.

## Verification

| Check | Coverage | Result |
|---|---:|---|
| Independent transport oracle | 817 presentations; 3,276 component pairs; 650,992 queries | Passed |
| Literal transport evaluation | 12,496 sheet-map checks | Passed |
| Independent canonical-key oracle | 285 presentations; 6,356 signature queries; 1,034 marking classes | Passed |
| Canonical witness evaluation | 44,790 sheet-map checks | Passed |
| New maintained tests | 9 tests, including 50,666 literal reflection/point comparisons | Passed |
| New tests with both existing surface-cover suites | 26 tests | Passed in 3.142 s |

The transport oracle materializes generator permutations and propagates
equivariance by breadth-first search. The canonical-key oracle enumerates
the resulting map actions on peripheral cycles. Expected answers use neither
gcd/CRT formulas nor the production component classifier or canonicalization.

The 650,992 transport queries comprise 3,276 unmarked, 19,336 point, 38,076
boundary, 295,152 double-boundary, and 295,152 mixed queries. That audit took
6.715 s. The canonical audit took 0.123 s. These are local validation timings,
not estimates of a knot-recognition running time.

Machine-readable evidence:

- `audit-results.json`
- `canonical-audit-results.json`
- `benchmark-results.json`

## Benchmark scope and selected measurements

Prepared-query medians use 11 repetitions and exclude parsing and cover
preparation. Preparation is recorded separately for the large binary inputs.
The literal comparator explicitly labels peripheral permutation orbits and
scans all possible root images. It measures the cost of expanding this local
covering problem; it is not a complete unknot recognizer or a comparison with
general Agol–Hass–Thurston algorithms.

| Model | Exact answer | Prepared compressed query | Literal scan |
|---|---:|---:|---:|
| 1,048,576 sheets, two cyclic boundary constraints | 128 maps, one progression | 5.929 microseconds | 0.761936 s |
| `W = 2^12000 * 3^12000 * 5^12000` (58,883 bits) | `5^12000` maps, one progression | 0.015027 s | Not expanded |
| Paired model with a 48,001-bit sheet count and one reflection boundary | 2 maps, two progressions | 0.004891 s | Not expanded |

The 58,883-bit example took 0.004245 s to prepare. All timings are
machine-specific; the proven bit bound is independent of them.

## Exact commands

The scripts accept `PROVEIT_FAST_ROOT`, naming the directory containing
`fastunknot/boundary_transport.py`. An existing `PYTHONPATH` also works.
Without either, they locate common repository/package layouts relative to
their own directory. They contain no machine-specific absolute paths.

From a repository root, for example:

```bash
export PROVEIT_FAST_ROOT="$PWD/Topology/UnknotRecognition/fast"
python research/boundary_transport/audit.py --output research/boundary_transport/audit-results.json
python research/boundary_transport/audit_canonical.py --output research/boundary_transport/canonical-audit-results.json
python research/boundary_transport/benchmark.py --output research/boundary_transport/benchmark-results.json
```

If this directory is distributed separately, use its actual location in the
commands and set `PROVEIT_FAST_ROOT` to the packaged `fast` directory.

Run maintained tests from `PROVEIT_FAST_ROOT`:

```bash
python -m unittest tests.test_boundary_transport tests.test_surface_cover tests.test_surface_cover_production
```

The standalone JSON query, also run from that directory, is:

```bash
python -m fastunknot.boundary_transport /path/to/example-query.json
```

The supplied example returns the ten root images `29 + 36*j`, for
`0 <= j < 10`. JSON accepts exact integers and the repository's signed
hexadecimal integer transport. `--seconds` requests cooperative cancellation.

## Limits and integration decisions

All maps are over the same fixed base surface and chosen peripheral paths.
A whole-circle correspondence does not require its representative sheets to
map to one another. The component-selector sheets are not additional marks.
Mark lists are ordered and may repeat circles or points.

The output does not certify ambient embeddings, arbitrary attaching maps,
parametrizations, or prescribed orientations/fibre directions. In particular,
an orientation constraint may matter for an orientable cover of a
nonorientable base. Extracting the promised cover presentation from a normal
surface remains a separate task. The cyclic signature method deliberately
rejects presentations with negative affine signs; general dihedral comparison
uses the transport solver instead.

Cancellation propagates as an exception, never as “no compatible maps.”
Individual large-integer operations and bulk serialization are not
hard-interruptible.

Fast local equivalence alone does not bound the number of states visited by
a hierarchy. The exponential whole-circle example has genus `W/2` and hence
does not contradict the bounded-Euler local theorem. Two point phases can
still encode `W` different states on an annulus. A global quasi-polynomial
recognition theorem must additionally control geometric extraction,
presentation diversity, gluing data, correction depth, and all intermediate
encoding sizes.
