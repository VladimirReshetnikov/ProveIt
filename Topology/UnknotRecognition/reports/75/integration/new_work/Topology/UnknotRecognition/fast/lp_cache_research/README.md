# Exact witness screening for quadrilateral propagation

This package adds `fastunknot.normal_propagation_cached.search_positive_euler`.
The existing producer and all integration defaults remain intact. The new
producer omits a coordinate-deletion LP only when an independently checked
integer positive-Euler witness already proves that deletion feasible.

```python
from fastunknot.normal_propagation_cached import search_positive_euler
from fastunknot.normal_propagation_verify import verify_normal_propagation_certificate

answer = search_positive_euler(triangulation, max_pivots=100000,
                               max_cached_witnesses=256)
if 'certificate' in answer:
    assert verify_normal_propagation_certificate(triangulation,
                                                  answer['certificate'])
```

The public statuses retain their original scope: they decide the existence of
an admissible positive-Euler normal surface with a zero triangle at every global
vertex. They are not by themselves an unknot verdict or a proof of provenance
from a knot diagram.

## Exact statement and policy preservation

For a fixed integer matrix `A`, objective `c`, and allowed column set `S`, write
`K(S)={x>=0: Ax=0, supp(x) subset S, c.x>0}`. If `w` belongs to `K(S)` and
`w[j]=0`, then `w` itself belongs to `K(S minus {j})`. In particular, every
coordinate mandatory for `K(S)` belongs to `supp(w)`.

The cache validates all coordinates, every equation `A w=0`, and strict
positivity of `c.w` with integer arithmetic. A global witness is reused only
when its complete support is contained in the new column set, including every
triangle anchor and every preceding branch/propagation restriction. A zero at
the tested coordinate alone is insufficient. Inclusion-minimal supports are
retained: if `supp(u) subset supp(v)`, every zero restriction covered by `v` is
also covered by `u`. Equivalently the zero sets form an inclusion-maximal
antichain. Optional finite storage evicts the oldest retained witness after
dominance pruning; losing evidence only loses acceleration.

The current-node LP is always computed from scratch. Its exact witness is
retained separately for the duration of that scan, including when global
storage is disabled (`max_cached_witnesses=0`). Therefore one scan calls the LP
solver at most once for each unresolved quadrilateral coordinate that is
positive in its current witness. Further witnesses can only reduce that count.

The original tetrahedron/type scan order and first mandatory choice are
preserved. Any omitted LP would have answered `POSITIVE`; all negative LPs are
still solved with the same ordered columns by the same deterministic engine.
Current witnesses, conflict choices, branch trees, final coordinates, and
negative dual vectors consequently agree when both runs can follow their
common trace. Complete certificates are equal, not merely equivalent. Under
the same finite pivot budget the screened producer may reach farther, so equal
status and equal node counts are not promised after budget exhaustion.
More precisely, with identical node/depth/pivot limits and no external
time/cancellation cutoff, completion by the baseline implies completion by the
screened producer with exactly the same certificate: it has spent no more
pivots before any unskipped query on their common trace.

The bounded exact Bland simplex engine is unchanged. No polynomial pivot
bound, general quasipolynomial recognition algorithm, or triangulation theorem
is claimed by this module.

With capacity `H`, the stored evidence consists of at most `H` integer vectors
and their supports. Each antichain comparison is a bit-mask inclusion test;
each newly accepted witness is checked against the original integer matrix.
The default fixed `H=256` bounds storage and lookup overhead polynomially in
model dimension and witness bit length. If `H=None`, the antichain can be
exponentially large; no small-antichain theorem is assumed.
For an explicit positive-kernel example, impose `a[i]+b[i]=z` for `r` pairs,
with all coordinates nonnegative and objective `z>0`. Every minimal positive
support contains `z` and exactly one variable from each pair, so there are
exactly `2^r` pairwise incomparable minimal positive supports in dimension
`2r+1`. Each is witnessed by setting its supported coordinates equal to one.

## Algebraic quadratic-to-linear LP-call family

`synthetic_family.py` explicitly replaces model construction and final geometric
analysis inside a research harness. Its cones are **not asserted to come from
triangulations**, and their synthetic certificates are not submitted to the
topological certificate verifier.

For positive integer `r`, arrange seven-coordinate blocks as follows:

1. `r` irrelevant prefix blocks, all of whose columns and objective entries
   are zero.
2. `r` mandatory blocks, whose first two quad variables are `q[j,0]`, `q[j,1]`.
3. `ceil(r/4)` auxiliary blocks, supplying distinct triangle variables `p[j]`.

Let `z=q[0,0]`. The equations are `q[j,0]=z` for `j>0` and
`q[j,1]+p[j]=z` for all `j`. The objective is `z`. All other columns are zero.
There are `t=2r+ceil(r/4)` blocks and `2r-1` equations.

The two columns for `q[j,1]` and `p[j]` are identical, including the
normalization row and objective coefficient. The former has smaller original
variable index. As long as it is present, the latter never enters a Bland
basis: while both are nonbasic their columns and reduced costs agree, so Bland
selects the earlier one; while the earlier is basic the later has reduced cost
zero. The assertion remains true under all previous pivots. Thus every
positive witness returned by the specified exact solver has `p[j]=0` whenever
`q[j,1]` is still allowed. Such a block has `q[j,0]=q[j,1]=z>0` and conflicts.

At each of the `r` propagation stages the baseline tests all `3r` irrelevant
prefix quad coordinates, then tests the type-0 coordinate of the first
unresolved mandatory block. That final deletion makes positive objective
impossible. After it is propagated the corresponding `p[j]` replaces the
forbidden type-1 variable. Following all `r` propagations the current witness
is admissible. Thus the exact call counts are

`baseline = (r+1) current-node LPs + r(3r+1) deletion LPs = 3r^2+2r+1`,

`screened = (r+1) current-node LPs + r mandatory deletion LPs = 2r+1`.

Screening uses only the current witness for this family. The formula therefore
holds even with global cache capacity zero. Both producers return the same
final certificate. This is a separation in expensive oracle calls, not a
general running-time theorem for Bland simplex.

The exact solver's pivot counts can also be determined for this family:
`baseline = 6r^3+3r^2+r` and `screened = 3r^2+r`. The full dictionary induction
is in `pivot_proof.md`. Every positive LP uses `2r` pivots; deleting mandatory
block `j` uses `2j` pivots, including zero pivots when `j=0` deletes the objective
coordinate. These are theorems for the specified algebraic model, row/column
order, and exact solver. They do not bound Bland simplex on other inputs.

## Reproduction and evidence

Run all commands from the `fast/` directory:

```bash
python -m unittest tests.test_normal_propagation_cached -v
python -m lp_cache_research.audit --rounds 3 --timeout 35 --figure-pivots 600 --output lp_cache_research/results.json
python -m lp_cache_research.replay --output lp_cache_research/replay_results.json
```

The last command is an independent replay of the saved evidence. It imports
the unchanged verifier and its low-level dependencies under a private package
namespace, avoiding the broad package initializer. It imports neither
propagation producer, the LP solver, audit/search scripts, nor Regina, and
runs no searches or native constructors. The recorded execution verified all
seven saved genuine completed certificates (six positive and one negative),
checked all 42 paired-sample certificate-digest references and 10 genuine
source digests, and reconciled all 15 compact summary rows. The three genuine
inconclusive cases and five synthetic algebraic certificates are expressly
excluded from certificate replay. Exact counts, dependency/source hashes, and
the actual replay result are saved in `replay_results.json`.

The focused suite covers exact validation, antichain dominance, anchor and
sibling restrictions, input immutability, bounded storage, corrupted positive
witness rejection, exhausted budgets, branch policies, positive and negative
certificate equality, and the algebraic call-count formulas. Regina is
optional for the native-topology test; the producer, frozen fixture replay,
and other tests use the standard library.

`triangulations.json` freezes the branching solid torus, finite trefoil,
native-generated finite figure-eight exterior, and both prior finite
figure-eight labels. Their face pairings and isomorphism signatures are saved.
The audit also regenerates a native finite figure-eight from
`Regina Example3.figureEight(); idealToFinite(); simplify()` and compares each
baseline/screened pair on exactly the same generated source. The audit records
its full source, signature, input digest, Regina version, and equality or
inequality with the saved native source. Simplification may produce different
finite triangulations of the same prescribed manifold across process histories
or Regina versions, so neither labels nor isomorphism signatures are assumed
to agree with a freshly regenerated source. Each frozen source is checked
against its own saved signature, and native export/import is checked by exact
round trip.

`results.json` contains three alternating-order samples per case, exact LP
calls/pivots/tableau-update counts, full completed certificates and their
digests, independent-verification outcomes, explicitly bounded inconclusive
figure-eight runs, source-code digests, and median wall times. Wall time is
descriptive and was measured in a shared execution environment without CPU
isolation; tiny cases can regress from cache overhead. The figure-eight
controls prominently expose the remaining node-LP bottleneck: at 600 pivots
they have no deletion queries for screening to remove. An inconclusive run is
never counted as a completed negative certificate or a recognition speedup.

## Integration scope

Required additive runtime file: `fastunknot/normal_propagation_cached.py`.
Dependencies are the existing `normal_propagation`, `exact_lp`, and
`normal_surface_geometry` modules. The existing independent
`normal_propagation_verify` accepts the unchanged certificate schema.
Tests and reproducibility material are under `tests/test_normal_propagation_cached.py`
and `lp_cache_research/`.

The fork was constructed from the producer with SHA-256
`147f4b504756036f0c56999f9f8e34747c20f9e36014b9361f1261428cbbc905`.
`create_cached_module.py` is an optional one-time audit aid, not a runtime
dependency; it refuses to regenerate against an unrecognized baseline.

## Further mathematical and algorithmic questions

1. Construct an explicitly triangulated family exhibiting a provable
   superconstant deletion-LP reduction. The algebraic family here does not
   establish that such a cone can arise from normal matching equations.
2. Bound the number or width of minimal feasible positive supports in special
   normal-surface cone families. General antichains can be exponentially large,
   so global cache size cannot simply be assumed polynomial.
3. Relate support screening to the size of a quadrilateral propagation
   backdoor. Fewer LP calls per state do not bound the number of branch states.
4. Reduce the first node LP cost exposed by the figure-eight controls, using
   exact equality-row reduction and a checked dual-lifting map. Such a method
   can preserve mathematical certificates without preserving their bytes.
5. Find a deterministic bounded portfolio of positive rays that jointly
   screen many coordinates while avoiding expensive witness discovery. The
   current algorithm reuses rays already needed by the original search.
6. Extend evidence reuse to negative duals only after checking their
   inequalities on every newly allowed column. This can change the exact
   negative proof tree and therefore belongs to a separate compatibility mode.
