# Exceptional-row forest research

This module solves a finite problem: choose a spanning tree in a supplied
rooted multigraph, delete its matrix rows, and completely peel the remaining
unsigned occurrence matrix on private unit columns. It does not authenticate
a triangulation, classify a manifold, or decide a knot type by itself.

The complete proofs and experiments appear in **Exceptional Rows and Fast
Certificate Replay for Unknot Recognition**, 12 October 2026. The baseline
repository revision is `c6d0ec8aa0b6308310ab6c081ba29d8bc363ede5`.

## Exact input

```json
{
  "vertices": 2,
  "columns": 2,
  "edges": [[0, 1], [0, 1], [0, 0]],
  "rows": [[[0, 1], [1, 1]], [[0, 1], [1, 2]], [[0, 1]]]
}
```

Every row has a corresponding edge. Root vertex is zero; a loop or `null`
edge is unavailable to a spanning tree. Sparse column indices in each row
must be distinct, and all stored counts are positive integers. Counts are
actual unsigned occurrences. The decision procedure caps counts at two;
that operation is not suitable for source-parity calculations.

## API and independent replay

```python
from triple_forest_research.nonlinear import solve_boolean, solve_width
from triple_forest_research.base_verify import verify

result = solve_width(problem, max_work=5_000_000, max_states=100_000)
# Alternative: randomized discovery with a deterministic certificate.
result = solve_boolean(problem, max_work=20_000_000,
                       max_states=100_000, trials=2)
if result['status'] == 'SUCCESS':
    assert verify(problem, result)
```

The discovery functions produce a tree and a complete pivot order. Call the
separate checker before relying on the result. The checker imports no
discovery code and reads the original graph and matrix. Every positive in
the delivered audits is independently replayed.

`solve_width` is deterministic and exact when uncapped. `solve_boolean`
has one-sided witness misses: a zero evaluation is `INCONCLUSIVE`, never a
negative proof. `seed=None` uses system randomness; an integer seed is
provided only for reproducibility. The mathematical probability guarantee
assumes independent uniform field samples. The default prime is `2**61-1`;
the finite implementation checks a 64-bit prime domain and rejects a prime
too small for the edge-copy construction. The asymptotic theorem chooses a
suitable growing prime. Resource limits always yield `INCONCLUSIVE` if they
interrupt search. A deterministic precheck can finish without enumerating
any ideal states.

The deterministic solver's exhaustive `NO_FOREST` is a finite algorithmic
conclusion. Except for source disconnection, this implementation does not
export a portable negative proof for all such conclusions. Passing that
result to the independent checker therefore does not turn it into a
certified negative. Source geometry and complete native terminal topology
remain additional obligations in every case.

## Parameters and algorithms

Let `m` count rows, `N` the explicit encoded input length, `k` the number of
useful exceptional columns, `d` the nonfree ordinary SCCs meeting their
supports, `J` the ideals of the resulting reachability poset, and `w` its
width. A column is useful if some entry equals one; useful columns of support
at least three are exceptional.

| Entry point | Bound | Scope |
| --- | --- | --- |
| `nonlinear.solve_boolean` | `J poly(N)`, `J <= 2**d` | Arbitrary useful support; one-sided randomization |
| `nonlinear.solve_width` | `J (m+1)**w poly(N)` | Deterministic, polynomial space |
| `solver.solve` | `3**k k! (m+1)**(2k) poly(N)` | Useful support at most three; exact fallback |
| `solver.solve_randomized` | `2**O(k log(k+2)) poly(N)` | Reference schedule/covering sieve |

For native triple-unit columns, `d <= 3k`, giving `8**k poly(N)` randomized
time. A width-`w` chain partition bounds `J <= (1+d/w)**w` for `w>0`.
Thus fixed width gives a deterministic polynomial local algorithm.
These are not general quasi-polynomial unknot-recognition theorems.

## Command line

From a directory whose Python path contains this package:

```sh
python -m triple_forest_research.nonlinear input.json --seed 20261012
python -m triple_forest_research.nonlinear input.json --deterministic-width
python -m triple_forest_research.solver input.json
```

The unchanged `base.py` and `base_verify.py` are attributed in
`ATTRIBUTION.md`. A future native adapter must export the exact source matrix
and transport the lower forest and all attachment data before treating the
finite certificate as a geometric statement.
