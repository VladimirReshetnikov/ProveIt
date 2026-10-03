# Five constructor-coordinate eliminations in finite eager Tree certificates

The complete [source](eager_tree_constructor_projection.py) projects five unconditional constructor coordinates out of each row of the frozen [strictly forward-pointer certificate](eager_tree_triangular_projection.md). It saves **15N operations and 5N natural witnesses** at each fixed external row count N, while increasing the exact complete polynomial degree from four to ten. The full natural zero fibers are in bijection with those of the triangular parent, and the represented natural `(program,argument,output)` triples are unchanged.

The selective schedule has

```
natural witnesses = (3N^2+23N)/2,
residuals = 17N+3,
M = (9N^2+91N+6)/2,
A = 6N^2+51N+17,
complete operations = (21N^2+193N+40)/2,
exact degree = 10.
```

These counts include all constructor arithmetic, pointer lookups, local/root residuals and the complete sum-of-squares finalizer. The three external scalar parameters are not counted as witnesses. N remains external. This is a finite-certificate cost/degree tradeoff, not a fixed-arity universal Diophantine polynomial, an ordinary-input recoder, or a unique computation-fiber theorem.

## Unconditional natural graph and exact source projection

Use the actual original coding polynomial

```
F(u,v)=(u+v)(u+v+1)+2v+2,
S(u)=2u+1.
```

The triangular parent retains the five graph equations in each row:

```
d=F(a,b),
e=F(a,y),
q=F(0,b),
j=F(S(a),b),
k=F(d,c).
```

They are unconditional equations, not guarded by the selected application tag. All their right sides are already computed and paid in the parent source. They form an acyclic sequence: only k uses an earlier removed coordinate d. For any natural retained tuple, these definitions uniquely restore all five coordinates as natural numbers. Indeed F(u,v) is at least two on naturals. Neither Boolean tags, active pointers, the local application equations nor a zero-set assumption is needed for this restoration.

The compiler replaces each supplied coordinate by the register holding its already computed right side, in dependency order. It substitutes the computed d into k's already emitted constructor arithmetic. It then removes the five private definition-subtraction gates and their residual entries. No constructor calculation is deleted, duplicated or treated as a free operation; the aliases are wires to existing paid source registers. The remaining source is closed and every gate and supplied field is live.

Let R be this polynomial restoration map, which leaves every retained coordinate and the external triple unchanged. The source transformation gives the literal whole-polynomial identity

```
F_child(v)=F_triangular_parent(R(v))
```

on all scalar tuples, including signed and rational tuples, and algebraically over any commutative ring. Every deleted definition residual becomes identically zero; each retained residual becomes its exact child residual. This is a graph-substitution identity between polynomials with different supplied-coordinate lists, not a same-coordinate polynomial identity.

On natural zeros, R and coordinate deletion are inverse maps. For the forward implication, R is natural-valued and the complete graph identity transfers a child zero to a parent zero. Conversely, a parent natural zero makes each of its SOS residuals zero, so the five equations force exactly R and permit deletion. This proves a bijection with the **entire triangular parent's** natural zero fibers at the same N, not merely existential equivalence of a selected subset. Combining with the earlier triangular normalization theorem preserves represented triples of the original height and occurrence-flow certificates; it does not create a bijection with all their unnormalized witnesses.

## Complete literal cost

The parent has `(3N^2+33N)/2` witnesses and `22N+3` residuals. Deleting the five coordinates and their defining rows in each local block gives the stated new interface counts.

Exactly 5N subtraction gates disappear from the certificate source. All multiplication and other addition gates remain. The complete finalizer then has 5N fewer residual squares and 5N fewer additions in its final sum; it is nonempty for every N>=1. Thus the exact full saving is

```
5N M + 10N A = 15N operations.
```

Subtracting this from the pinned parent's complete ledger gives the headline formula. This conclusion uses the actual literal schedule, rather than a local expression estimate that forgets the finalizer. The separate inherited `cleanup=True` option also omits the parent's already identified `0+b` operations, saving another N additions. The constructor projection saves exactly 15N in either mode and does not claim an optimized circuit.

| N | Witnesses | Residuals | Selective operations | With static cleanup |
|---:|---:|---:|---:|---:|
| 1 | 13 | 20 | 127 | 126 |
| 2 | 29 | 37 | 255 | 253 |
| 3 | 48 | 54 | 404 | 401 |
| 4 | 70 | 71 | 574 | 570 |
| 5 | 95 | 88 | 765 | 760 |
| 6 | 123 | 105 | 977 | 971 |
| 7 | 154 | 122 | 1210 | 1203 |
| 8 | 188 | 139 | 1464 | 1456 |

The [receipt](eager_tree_constructor_projection.json) contains all 16 complete emitted sources, interfaces and ledgers.

## Exact degree

The restored d,e,q,j have degree two, while k=F(F(a,b),c) has degree four with highest part `(a+b)^4`. The local constructor-input residual is

```
x - [t1*S(a)+t2*q+t3*j+t4*k].
```

Its degree-five highest part is `-t4*(a+b)^4`. Every other retained residual has degree at most three: in particular the e-dependent output residual is `t1*(z-F(a,y))`, while the pointer lookups remain quadratic. Therefore the entire highest homogeneous part of the child SOS is exactly

```
sum_(i=0)^(N-1) t[i,4]^2*(a[i]+b[i])^8.
```

It is nonzero for every N>=1. The coefficient of `t[0,4]^2*a[0]^8` is one, so the exact complete degree is ten, including N=1. This is the polynomial's formal degree on its full supplied-coordinate domain. For example, no additional equation forcing a particular tag to zero on a small zero set is substituted when computing that degree.

## Authenticated API and bounded evidence

The source authenticates the unchanged triangular source/receipt/note at hashes `a3b528c0…`, `79abbc08…`, `28e96fdc…`, the unchanged occurrence-flow trio at `0f2e8a49…`, `10fd1875…`, `ae46bd1c…`, and the original placed kernel at `636ce7fe…`. All full SHA-256 values are in the source and receipt. Authentication occurs on every public build or check; source is compiled directly from authenticated bytes, with no shared mutable packet cache.

`build(N,cleanup=False,root=...,repo=...)` emits the complete child. `canonical_parent` returns the matching triangular packet. `rewrite` requires the whole canonical parent; `checked`, `polynomial_source` and `evaluate` validate the whole child. `restore_constructors` returns the complete triangular assignment. `project_parent_zero` requires a complete natural parent zero and returns the child assignment, checking the unique inverse. Public assignment APIs accept exact integers, including zero, and reject bool/float aliases. `signed=True` enables integer polynomial evaluation/restoration without a signed-domain computation claim; rational cases are checked only by the internal algebraic evaluator.

The checker proves full coefficient-dictionary graph identities for both schedules at N=1,...,8, verifies every retained and removed residual, independently matches each actual constructor RHS to the displayed polynomial graph, and checks the entire exact degree-ten leader. Evaluated signed and rational identities supplement these proofs. Genuine application certificates exercise all five eager rules, padded rows and cases requiring a nontrivial topological permutation through the already reviewed triangular normalizer, then round-trip through this new unique constructor graph. No historical broad suite is repeated.

Malformed-call, copy-isolation and source-pin checks use private copies only. Each of the six parent artifacts and the original kernel is changed after a successful private build and rejected; optimized Python execution is also rejected. The complete saved receipt is compared recursively with exact types.

Replay requires only the standard library:

```
python eager_tree_constructor_projection.py \
  --root /path/to/sibling-parent-artifacts \
  --repo /path/to/Proofs \
  --output /tmp/tree-constructor-replay.json \
  --expect eager_tree_constructor_projection.json
```

All frozen parent artifacts remain unchanged. The general graph, natural-domain and degree arguments above establish the infinite family; the finite emitted cases and test counts are supporting evidence, not substitutes for those arguments.
