# Independent review of the finite triangular eager Tree certificate

PASS. The frozen [author source](eager_tree_triangular_projection.py), [receipt](eager_tree_triangular_projection.json), and complete [proof note](eager_tree_triangular_projection.md) have no unresolved mathematical, source, ledger, or public-API finding. This review covers the triangular projection only; the earlier root-only projection is a separate construction.

The authenticated author hashes are:

- Python: `a3b528c0ed9434ab95cf1705146a6cc287a9cf9fceb7c14f0062f042219788e2`.
- JSON: `79abbc089bac5648e7dad0c1a41fd40572f9fd4ffad7433209cbd4a954bc9cc1`.
- Markdown: `28e96fdcca087b4263cf88edfe19a9116b1842b2df792f0068659ec47c9028c3`.

The [independent checker](review_eager_tree_triangular_projection.py) and [receipt](review_eager_tree_triangular_projection.json) also authenticate the frozen occurrence-flow parent trio, the actual corrected original kernel, and the earlier [manual occurrence-flow review source](review_eager_tree_occurrence_flow_full.py). That last helper supplies the independent handwritten complete height/flow schedules, exact-expression interning, liveness counter, and bounded genuine-certificate utilities. This reuse is explicit: the new checker does not call the author's rewrite, coefficient prover, or verification routine to establish its identities. It reconstructs the triangular schedule by its own substitution and pruning routine, performs its own sparse polynomial arithmetic, and checks the actual author packets. The earlier elimination scout is not a replay dependency.

## What the zero theorem preserves

Let `A_ij` be the sum of the three premise-slot selectors from row `i` to row `j`. At a natural flow zero, `mu=e_0+A^T mu` implies a positive mass on every root-reachable vertex. A reachable directed cycle is impossible: its nonnegative balance inequalities force equal masses around the cycle and exclude any positive inflow, contradicting either the root injection or the first entry of a root path. Thus the reachable rows form a DAG even though unreachable cyclic components may remain.

Replacing all unreachable rows by a valid leaf does not alter any reachable premise lookup. Topologically order the reachable rows parent before premise, keep the root first, and put the dummy rows afterward. Permute every row field and every pointer target column together; premise-slot order and multiplicities stay intact. Each surviving edge then has target index strictly greater than its source index. The external scalar `program`, `argument`, and `output` bindings stay unchanged. Existence of this reordered witness proves completeness at the same external `N`; it is not a free sorting subcircuit used by the polynomial.

Conversely, the child permits only pointers `p[i,s,j]` with `j>i`. Natural tags and active-slot sums retain their original exact case-selection meaning. Backward induction on row index applies the unchanged eager Tree rules. The child therefore represents the same natural triples at each `N`.

Neither normalization nor this theorem gives a bijection with all parent zeros. Unreachable rows can change, and row permutations can change presentations. The review includes a complete parent zero with root mass **5**, caused by unreachable circulation feeding the root; its normalized restoration has root mass **1**. Merely deleting coordinates from that parent zero would not preserve its witness. The existing canonical unique-fiber refinement is not inherited.

## Both complete polynomial graph identities

Hardwire every forbidden pointer to zero. For arbitrary child coordinates define, recursively,

```
mu_i = delta_i0 + sum_(j<i,s) mu_j*p[j,s,i],
h_i  = 1 + sum_(j>i,s) p[i,s,j]*h_j.
```

The flow recursion is evaluated forward and the height recursion backward. They uniquely solve the respective parent rank equations over any commutative ring. The actual parent rank residuals have exactly these coefficient schemas. Every other parent residual contains no rank coordinate and equals its corresponding literal child residual after the zero-pointer substitutions. Consequently the **full** child SOS polynomial equals each complete parent polynomial after its recursive graph substitution. This is an all-value identity, not only a zero-set implication or an equality of a routing fragment.

For natural child tuples, restored masses are nonnegative and restored heights are positive, before assuming any other zero equation. Each restoration thus gives a natural-zero bijection with the corresponding parent's strictly triangular slice. It gives no computational interpretation to signed or rational tuples; those domains are used only to check polynomial identities. The restored coordinates are absent from the emitted child's input and source, so their proof/API computation contributes no hidden child-evaluation gates.

The checker independently verifies all retained coefficient identities, every original rank schema, and exact recursive cancellation of the deleted rows for `N=1,...,8` in both cleanup modes. Literal finalizer equality then proves both whole-polynomial graph identities. The general recurrence argument above establishes the family theorem beyond these finite instances.

## Full ledgers and exact degree

For a row with `m=N-1-i` allowed targets, pointer work is `9m` multiplications and `12*max(m,1)` additions. At `m=0`, all twelve `0-target` residual subtractions remain paid. The remaining local comparison source costs `33N` multiplications and `45N+3` additions. No CSE, sign normalization, residual deduplication, or input-decoding allowance is used.

The selective schedule therefore has

```
witnesses = (3N^2+33N)/2,
residuals = 22N+3,
comparison M = (9N^2+57N)/2,
comparison A = 6N^2+39N+15,
full M = (9N^2+101N+6)/2,
full A = 6N^2+61N+17,
full operations = (21N^2+223N+40)/2.
```

The finalizer pays one square per residual and one fewer final additions. The separate static-cleanup schedule removes exactly `N` already-existing `0+b` gates. It is reported separately from substitution-affected simplification. In particular, `N=1` costs `142` or `141`, with 18 natural witnesses and 25 residuals. Selective totals at `N=2,5,8` are `285,840,1584`.

All surviving residuals are quadratic. The retained row `d_0-F(a_0,b_0)` has quadratic part `-(a_0+b_0)^2`. A real sum of squares of highest quadratic parts cannot cancel identically, so the complete degree is exactly four for every `N>=1`, in both cleanup modes. The checker verifies this particular nonzero highest part against the actual coefficient expansion, not merely a syntactic degree bound.

The prior article allows arbitrary row ordering with height witnesses. Its canonical refinement sorts nonroot input keys by numerical code, retains the height kernel, and pursues uniqueness. The bounded earlier source scan did not find this triangular deletion there. No repository-wide novelty or arithmetic-optimality claim follows.

## Independent execution and public boundaries

The saved review checks all 16 published complete forms (`N=1,...,8`, two modes), including every paid gate's liveness and the complete finalizer. It records 1,632 independent literal residual-DAG identities, 3,264 retained coefficient identities, 144 actual parent rank schemas, and 144 recursive cancellations, yielding 32 full parent graph proofs. It also checks 320 whole graph evaluations, including 128 signed-integer and 64 rational evaluations, and 256 calls to the public restoration APIs.

There are 130 genuine application normalizations with root-fixed row permutations and padding; 28 specifically demonstrate that naive backward-pointer deletion fails. Two full disconnected-cycle zeros and two root-inflation normalizations challenge the existential-versus-bijection distinction. These fixtures use a few calls to the authenticated original evaluator, not its historical main suite.

The API checks require exact integer `N`, exact Boolean mode flags, complete canonical packets, complete exact-integer assignments, and natural coordinates by default. They reject changed metadata, nested float/Boolean aliases, tuple/list substitutions, missing or extra coordinates, negative natural values, and nonzero parent inputs to zero-only projections. Returned packets and assignments are independent copies. The checker also changes actual parent/kernel bytes after successful calls, verifies rejection on six subsequent entrypoints, and verifies that forged timestamp/size-compatible bytecode and preloaded module stubs cannot substitute for authenticated source bytes. Optimized `python -O` is rejected explicitly.

The certificate remains a finite circuit family with external `N` and natural coordinates including zero. It supplies neither a fixed-arity universal bound nor a paid ordinary-input loader. Those restrictions agree with the author note and current packet metadata.

Standard-library replay, with the author trio, parent trio, and committed manual review helper in the same artifact directory:

```sh
cd /
python /path/to/review_eager_tree_triangular_projection.py \
  --repo /path/to/Proofs \
  --artifacts /path/to/sibling/artifacts \
  --expect /path/to/review_eager_tree_triangular_projection.json
```

The author artifacts and repository files were not edited. Writer and fresh exact saved-receipt replay passed; this review requests no correction.
