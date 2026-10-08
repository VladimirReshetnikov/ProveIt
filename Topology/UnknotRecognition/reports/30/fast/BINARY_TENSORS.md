# Exact binary tensors and compressed transport

Research continuation of 8 October 2026, against ProveIt commit
`8a95834940cf77cdab1b39571ffc102ca8b6bede`.

This change has three mathematical components and one independently diagnosed
subprocess compatibility correction. The accompanying article gives complete
proofs, bit-cost accounting, measurements, limitations, and twelve research
questions. A general quasi-polynomial unknot recognizer is **not** established.

## Full Jones polynomial with binary edge orientations

```sh
python -B -m fastunknot jones examples/trefoil.json --backend spin-faithful
python -B -m fastunknot recognize examples/conway.json --jones-backend spin-faithful
```

The new optional backend is integrated into the selector, recognizer, and
full-polynomial command. It preserves the normal front-end order and exact
fallback. A nonidentity Jones polynomial proves nontriviality; identity by
itself remains inconclusive. Earlier structural filters can decide a diagram
before this backend runs.

```python
from fastunknot import Diagram
from fastunknot.spin_jones import spin_jones_exact, verify_turn_certificate

d = Diagram.from_braid(3, [1, -2] * 5)
result = spin_jones_exact(
    d, include_polynomial=True, max_states=None, max_transitions=None,
)
assert verify_turn_certificate(d.pd, result['turn_certificate'])
print(result['jones_polynomial'])
```

For an actual maximum frontier of `w` edges, there are at most `2**w` keys and
`poly(n) * 2**O(w)` deterministic bit operations. The existing certified
separator order gives `poly(n) * 2**O(sqrt(n))` full-polynomial computation
when local caps and external deadlines are absent. This improves the
maintained faithful Potts implementation's proved bound. Comparable general
quantum-invariant complexity bounds are already established by
[Maria (2021)](https://doi.org/10.4230/LIPIcs.SoCG.2021.53); no general-complexity
priority claim is made.

An integral edge-turn cochain is constructed from the PD rotation system and
checked by an independent face-equation verifier. The tensor weights sum the
two orientations of each smoothing circle. A boundary-phase lemma permits one
signed integer and one phase per key. A faithful integer specialization and
balanced-digit decoder recover the full polynomial. Intermediate integers
have polynomial bit length. The decoder checks normalization consistency;
it is not an independent verifier of the entire state sum.

The backend remains optional because benchmarks include substantial
regressions. On one 144-crossing grid, ordinary full-query medians improve
from 313.118 to 186.080 ms; on a 254-crossing tree medial, they regress from
66.662 to 305.133 ms. A 196-crossing grid completes with binary tensors while
Potts reaches the same state allowance. These are invariant queries, not
evidence of faster complete recognition of hard knots.

See [spin_jones_research/README.md](spin_jones_research/README.md) for exact
interfaces, caps, state counts, matched-order comparisons, and preserved
initial and follow-up implementations.

## Exact compressed matching with a bounded suffix deficit

The existing `CommonSubstring.longest` path gains a specialized branch after
its checked longest common prefix `K`. Write the word lengths as `K+a` and
`K+b`, and put `S=a+b-1`. For `a,b >= 1` and `K >= S-1`, every improvement is
covered by the `S` cut alignments `d=1-a,...,b-1`. Each long shifted comparison
reduces to a small-period cycle automaton on the grammar. Only bounded seed
and tail intervals are materialized.

The branch uses a conservative fixed gate `S <= 32`. Its post-prefix cost is
`O(g*S*S)` arithmetic/dictionary operations, with a conservative polynomial
deterministic bit bound for fixed `S`. All other inputs retain the existing
complete fallback. The improvement does not bound the number of group-search
moves or the growth of intermediate grammars.

The family `X=(ab)^N c T`, `Y=(ab)^N a T`, with
`T=aabbccacbabc`, defeats alphabet and directed-pair separation but is handled
by this branch. At `N=2**500`, the new complete query takes 92.580 ms in the
recorded audit; baseline and generic-LCE ablation reach the two-million-work
allowance. None of the fifteen whole-knot corpus queries activates this
branch, so no whole-recognition speedup is attributed to it.

See [near_prefix_research/RESULTS.md](near_prefix_research/RESULTS.md).
The benchmark loads the exact baseline module through a checked hash, using
the pinned git source or its archived copy:

```sh
python -B near_prefix_research/benchmark_near_prefix.py --fast-dir . \
  --output results/near_prefix_local.json
```

## Transporting whole boundary lifts in compressed covers

`BoundaryTransportIndex` extends the existing checked dihedral surface-cover
model. Given ordered point correspondences and unparameterized boundary-lift
correspondences, it returns all compatible covering isomorphisms in at most
two arithmetic progressions of root images. The post-preparation bound is
`O((k+1)*B**3)` bit operations for `k` constraints and `B`-bit integers.

The cyclic subcase also has complete canonical keys. For periods `q_i | m`,
the exact number of ordered marking types is `product(q_i)/lcm(q_i)`. For a
fixed connected cyclic component `C` and `k >= 1` whole-circle slots with
fixed base-boundary labels, the count is at most
`max(2,-chi(C))**(k-1)`. Polynomial Euler complexity and logarithmically many
slots give a local quasi-polynomial count. Bit-time claims additionally need
control of the covering presentation's encoded size.

The kernel compares maps over one fixed base presentation. It does not
retain arbitrary parametrized gluings, twist phases, prescribed component
orientations, or interval-fibre directions. It is not yet connected to a
complete geometric hierarchy constructor.

See [boundary_transport_research/INTEGRATION_NOTES.md](boundary_transport_research/INTEGRATION_NOTES.md)
for actual API examples and
[boundary_transport_research/RESULTS.md](boundary_transport_research/RESULTS.md)
for the literal permutation audits. Over 650,000 transport queries were
checked against a separate permutation-graph oracle.

```sh
python -B boundary_transport_research/audit.py --output results/boundary_audit_local.json
python -B boundary_transport_research/audit_canonical.py \
  --output results/boundary_canonical_local.json
```

## Subprocess compatibility correction

The first integrated test run exposed a defect that also reproduces in the
unchanged pinned baseline on the supplied Python 3.12.14 runtime. Repeated
`communicate(None)` calls after a short timeout strand unsent input from a
large payload. The fixed wrapper invokes `communicate(payload)` once in an
owned thread and polls completion for cancellation and local deadlines.
Cleanup kills/reaps the direct worker, joins the communication thread, and
closes the streams. The optional Regina stage remains an external-engine
verdict with unchanged trust labeling.

The controlled worker must not leave descendants inheriting these pipes.
The maintained worker satisfies that direct-worker model; this is not a
general process-tree supervisor. The correction was tested on Linux, with
Regina 7.4.1. Before/after source and diagnosis are included in the article's
validation artifacts. No Jones or word timing is attributed to this fix.

## Verification and next work

```sh
python -B -m unittest discover -s tests -v
python -B -m unittest discover -s tests -p 'test_spin*.py' -v
python -B -m unittest discover -s tests -p 'test_boundary_transport.py' -v
```

The archive's validation report records the exact final test count and
runtime, independent audit totals, baseline failure diagnosis, and patch
application check. Raw timing files retain censored statuses. Historical
measurement source is preserved instead of relabeling old measurements as
final-source runs.

The most useful next implementation experiments are minimizing turning
cochain size, charged backend selection, a direct cyclic near-prefix matcher,
and collection of real relator states activating the new branch. The main
mathematical obligations toward quasi-polynomial recognition are complete
compressed-cutting and repair interfaces, continuation-preserving geometric
canonicalization, and a bound on all distinct states and unary work in the
hierarchy. The article states these obligations explicitly.
