# Normalizing the root of the finite eager Tree certificate

For each fixed external `N>=1`, the [occurrence-flow parent](eager_tree_occurrence_flow.md) can be restricted to

```
mu_0=1,     p[j,s,0]=0 for every row j and slot s.
```

This eliminates `3N+1` natural witness coordinates. Its root balance becomes identically zero and is deleted. The complete emitted child represents exactly the same natural `(program,argument,output)` triples as the parent. The reverse relation is a bijection to this **normalized parent slice**, not a coordinate projection of every original zero. The external `N` is retained; no fixed-arity universality or unique witness theorem is asserted.

The [source](eager_tree_root_projection.py) pins the complete parent source at `0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c`, its receipt at `10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d`, and its note at `ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9`. The parent authenticates the actual corrected eager Tree kernel before generating its full source. No parent bytes are changed.

## Natural zero theorem

At any parent natural zero, the root-reachable graph is acyclic by the occurrence-flow theorem. Keep those rows, replace all unreachable rows by the existing valid leaf dummy, and recompute occurrence counts from one root injection. A reachable incoming edge to the root would give a cycle, so none exists. Dummy rows have no pointers. Therefore every incoming root pointer is zero, and the recomputed root mass is one. This gives a normalized parent zero with the same three external coordinates and the same number of rows.

Substituting these fixed coordinates in every original residual makes the root balance `1-1-0=0`. Deleting it and evaluating all other residuals therefore gives a child zero. Conversely, every natural child tuple restores a natural parent tuple by inserting the prescribed zero/one constants. At a child zero, every retained parent residual vanishes and the root residual is identically zero, so this restoration is a normalized parent zero. These directions prove equality of represented triples at each `N`, including `N=1` and padded certificates.

Unreachable rows must be handled before claiming this normalization of an arbitrary parent zero. They can carry circulation and send positive flow into the root. A six-row checked fixture has root application `(10,1014)->1014`, root mass three, and two incoming pointer slots from an unreachable cyclic row. Simply deleting the prescribed coordinates gives a child polynomial value `4112998`. Replacing unreachable rows by dummy leaves and recomputing the rooted flow gives value zero. Thus the graph normalization is substantive, and an unrestricted same-tuple projection would be false.

All supplied coordinates remain natural integers, including zero. The normalization proof uses the parent's natural selector and flow theorem. Signed evaluation below is only a polynomial interface; it does not assert signed-domain computation semantics.

## Literal source transformation and full accounting

The source substitutes the `3N+1` constants, applies exact constant arithmetic and the identities `0*x=0`, `1*x=x`, `0+x=x`, `x+0=x`, `x-0=x` in affected dependency cones, prunes dead gates, deletes only the root balance, and rebuilds the fully paid sum of residual squares. It does not make common-subexpression sharing or delete repeated residuals. In particular `0-x` remains a paid subtraction.

The default `cleanup=False` leaves unrelated parent source instructions literally present. A separately counted `cleanup=True` also removes the parent's existing `0+b` additions in its `F(0,b)` code constructors, one per row. That static cleanup needs no semantic projection and is recorded separately for a fair comparison.

Both schedules have

```
natural witnesses = 3N^2+16N-1,
quadratic residuals = 23N+2,
exact complete degree = 4.
```

For the default affected-cone schedule and `N>=2`,

```
M = 12N^2+41N+5,
A = 15N^2+53N+4,
complete operations = 27N^2+94N+9.
```

For `N=1` the complete source has `58M+84A=142` operations. The distinct formula is necessary: a one-entry pointer sum has no addition to remove.

Relative to the literal flow parent, the general reduction removes `15N-2` multiplications and `15N+2` additions for `N>=2`, hence exactly `30N` operations. This includes the omitted root square and finalizer addition. Explicitly: the complete root balance cone removes `3N` products and `3N+1` additions; root-column lookups remove `9N` products and `9N` sum additions; pointer row sums remove `3N` additions; setting the root mass to one removes `3(N-1)` remaining flow products; and the deleted finalizer term removes one product and one addition. At `N=1`, the sum-addition savings do not occur, so the saving is 18 operations.

The optional static cleanup saves another `N` additions in every case. Thus it has `27N^2+93N+9` operations for `N>=2`, and 141 at `N=1`. All gates, selector products, lookup sums, root external bindings and finalizer operations are counted.

| N | Natural witnesses | Residuals | Default operations | With static cleanup |
|---:|---:|---:|---:|---:|
| 1 | 18 | 25 | 142 | 141 |
| 2 | 43 | 48 | 305 | 303 |
| 3 | 74 | 71 | 534 | 531 |
| 4 | 111 | 94 | 817 | 813 |
| 5 | 154 | 117 | 1154 | 1149 |
| 6 | 203 | 140 | 1545 | 1539 |
| 7 | 258 | 163 | 1990 | 1983 |
| 8 | 319 | 186 | 2489 | 2481 |

On the graph of the inserted constants, the entire child polynomial equals the entire parent polynomial over arbitrary scalar assignments. This is an exact substitution identity, not just zero-set equivalence. The retained `d_0-F(a_0,b_0)` residual still has nonzero quadratic homogeneous part, while every residual is quadratic. Hence the complete SOS degree is exactly four, uniformly for every `N`.

## Interfaces and replay

`build(N,cleanup=False,root=...,repo=...)` emits the entire canonical source, witness interface, residuals and finalizer. `checked` rebuilds and compares the whole packet with exact types. `evaluate` requires a complete integer assignment and defaults to the natural domain; `signed=True` only enables signed integer polynomial evaluation. `restore` inserts the fixed coordinates on any supported assignment. `project_normalized_zero` requires a natural zero already on the normalized slice. `normalize_parent_zero` accepts an arbitrary parent natural zero, replaces unreachable rows, recomputes flow and returns a child zero. No shared mutable packet cache is used.

The [saved receipt](eager_tree_root_projection.json) emits both full schedules for `N=1,...,8`. Exact coefficient dictionaries prove 16 complete polynomial identities and 1,688 retained residual identities; 96 signed numerical identities supplement them. The checker also exercises 48 genuine application/padding projections, two disconnected-cycle normalizations, the incoming-root counterexample, 33 malformed-call rejections and four independent copies. These finite checks support the general graph and gate-count derivations above; they are not an unrestricted exhaustive verifier.

The standard-library replay takes explicit paths and performs no original suite runs:

```sh
python eager_tree_root_projection.py --root /path/to/sibling/parent/files \
  --repo /path/to/Proofs --output /tmp/tree-root-replay.json \
  --expect eager_tree_root_projection.json
```
