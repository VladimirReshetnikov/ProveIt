# Exact planar-sector research audits

Run these modules from the `fast` directory, with the source tree on Python's
import path. The core audit and certificate replay use the standard library
and the supplied `fastunknot` modules. `--fresh-regina` additionally uses the
installed Regina Python package; the retained run used Regina 7.4.

## Frozen complete-list comparison

```sh
python -m planar_sector_research.audit \
  --corpus /path/to/discovery_corpus.json \
  --output /path/to/results/corpus_audit.json \
  --fresh-regina
python -m planar_sector_research.replay \
  --certificates /path/to/results/planar_coverage_certificates.json \
  --output /path/to/results/corpus_coverage_replay.json
```

`audit.py` preserves the support-selection procedure from the incoming
`unknot_minimum_envelopes_20261009` bundle. Its docstring records the original
driver's SHA-256. The exact reference corpus has SHA-256
`0433e6c7d99bb402b79909467a7eada862ca004dc4082ee25794add0e712914e`.
Selection gives 9,995 distinct source/support pairs on its 48 triangulations.
The driver builds one `PreparedSectorSource` per triangulation, then audits
every selected sector of raw matching nullity at most three.

For each audited sector, the expected set is the complete frozen standard
vertex list restricted to its allowed quadrilateral coordinates, excluding
vectors with zero quadrilateral part. Equality concerns complete integer
coordinate vectors, not just cardinalities, support patterns, or Euler
characteristics. The output records every eligible support, oracle indices,
an exact ray-set hash, geometric statistics and the relevant proved output
bounds. Separate aggregate hashes bind both the finite selection and all
computed output sets. Any mismatch raises an error.

The optional eight fresh Regina runs regenerate *complete* standard vertex
lists on selected corpus triangulations with dimension-three cases. They
check that the retained oracle data agree with the installed Regina version.
Regina is an external cross-check, not an ingredient of the native solver.

Coverage samples include every observed pair of raw nullity and feasible
section dimension, including empty and degenerate sections. Additional
samples retain the largest ray list, the most active vertex groups and
essential discs absent from the quadrilateral vertex list. `replay.py`
imports only the independent coverage checker; it does not import the sparse
builder, polygon producer or ray enumerator.

The finite support selection is exhaustive on sources with at most three
tetrahedra. It is not exhaustive over all compatible sectors of the larger
triangulations. Raw nullity greater than three is explicitly recorded as
outside this solver's scope.

## Two-cap Fibonacci family

```sh
python -m planar_sector_research.family_audit \
  --sizes 1 2 4 8 \
  --output /path/to/results/double_cap_family_audit.json \
  --fresh-regina
python -m planar_sector_research.replay \
  --certificates /path/to/results/double_cap_coverage_certificates.json \
  --output /path/to/results/double_cap_coverage_replay.json
```

`fixtures.double_capped_fibonacci(n)` constructs an actual triangulated
solid torus with `n + 2` tetrahedra. It extends the attributed prior
one-cap fixture by attaching a second tetrahedral ball to the other original
boundary face. The sector allows type 2 in each original tetrahedron and
type 1 in both caps.

Let `A = F[n+1]`, `B = F[n+2]` and
`h = max(0, y - A*x, z - A*x)`. The rows, with triangle coordinates followed
by quadrilateral coordinates, are

```text
base i:  (F[n-i+1]*x+h, F[n-i+1]*x+h, h, h; 0, 0, F[n-i]*x)
cap one: (A*x+h-y, B*x+h, 0, h; 0, y, 0)
cap two: (B*x+h, A*x+h-z, h, 0; 0, z, 0)
```

The seven primitive parameter directions are
`(1,0,0)`, `(1,A,0)`, `(1,0,A)`, `(1,A,A)`, `(0,1,0)`, `(0,0,1)` and
`(0,1,1)`. The source matching nullity is three. The active minimum functions
are `0`, `A*x-y` and `A*x-z`; their section has three cells, three internal
edges and seven vertices. Thus this family attains the one-group bound
`3 + 2*(3-1) = 7` for every `n`.

The first four rays are meridian discs. The last three, including the ray
with equal nonzero cap coordinates, are inessential discs. More generally,
the displayed canonical vector represents `x` meridian discs and `h`
inessential discs. The article proves the all-size statement. The audit
checks the coordinate formula against the native matching model on a
deterministic grid, computes and independently replays compressed component
censuses for all seven rays and three mixed directions at each requested
size, and optionally asks Regina to classify each ray and regenerate its
complete standard vertex list.

The family audit records exact results and counts. It does not measure
running times. These scripts are not complete unknot-recognition benchmarks
and do not establish a global quasi-polynomial complexity bound.
