# Strictly forward pointers in finite eager Tree certificates

At every fixed external `N>=1`, the eager Tree certificate can restrict premise pointers to strictly later rows and omit all height or occurrence-flow coordinates. The resulting complete polynomial represents exactly the same natural `(program,argument,output)` triples. Its literal selective-cleanup ledger is

```
natural witnesses = (3N^2+33N)/2,
quadratic residuals = 22N+3,
M = (9N^2+101N+6)/2,
A = 6N^2+61N+17,
complete operations = (21N^2+223N+40)/2,
exact degree = 4.
```

These are complete finite-family counts, including pointer lookups and the sum-of-squares finalizer. `N` remains external; this is not a fixed-arity universal Diophantine polynomial, a paid ordinary-input decoder, or a unique-fiber construction.

The [source](eager_tree_triangular_projection.py) authenticates the frozen [occurrence-flow parent](eager_tree_occurrence_flow.md), source SHA256 `0f2e8a4912190ed8fd68f0f624d1d41bbc39b46bb992a68849019cd9fec3438c`, receipt `10fd18759cc09349d469e066cf1bba43e0a8ff0247b7e5646ee8f21576c9591d`, and note `ae46bd1c1f283654ff8aee06f80415ad6058e23f2c4471ad1e027f454db870b9`. That source authenticates and emits the corrected original height compiler as well. Neither parent is modified. This is separate from [root-only normalization](eager_tree_root_projection.md).

## What changes and why it is complete

For every row `i`, hardwire

```
p[i,s,j]=0 whenever j<=i, for all three premise slots s.
```

Only the `3N(N-1)/2` strictly upper-triangular pointer coordinates remain. Drop all `N` occurrence-flow rows and coordinates. Keep every constructor, tag, active-slot, pointer-lookup and root-binding residual, with the zero pointers substituted.

Soundness requires no extra rank witness: every selected premise has a larger row index. Backward induction on `i` proves the terminating eager application represented by each row. Natural tags sum to one and natural pointer lists sum to their active flag, so the retained equations still force the actual five local cases and exact premise choices. If a row has no later position available, its active-slot equations force a nonrecursive case.

For completeness from an arbitrary parent flow zero, first keep its root-reachable DAG and replace all unreachable rows by the valid leaf dummy. Then topologically order the reachable rows, with the root first, and put the dummy rows afterward. The root has no incoming reachable edge, and every other reachable row has a root predecessor path, so such a root-first order exists. Permute all row fields and pointer targets together. Every remaining selected edge points forward. This yields a child zero at the same `N` and with the same external triple. The original height parent similarly gives an acyclic graph and the same normalization.

The normalization can change unreachable rows and the order of other rows. It does not preserve all old witness tuples. In particular, arbitrary original rows cannot simply lose their backward pointers: the included application `(154,1)` needs a nontrivial permutation, and direct deletion fails. All domains are natural integers, including zero; no real-zero or signed-domain computation theorem is asserted.

## Exact graph restoration, beyond the zero-set theorem

On any child tuple with the forbidden pointers set to zero, define

```
mu_0=1,
mu_i=sum_(j<i,s) mu_j*p[j,s,i]          (i>0),

h_i=1+sum_(j>i,s) p[i,s,j]*h_j         (i descending).
```

The first recursion uniquely restores the flow parent's coordinates. The second uniquely restores the original height parent's coordinates. Every restored flow or height residual is identically zero over any commutative ring, without assuming Boolean selectors or the other equations. All retained residuals equal their literal child counterparts. Therefore the **entire** child polynomial equals each complete parent polynomial after its corresponding graph substitution, on all scalar tuples.

For natural child tuples the restored masses are nonnegative and the restored heights are positive. Thus each restoration gives a bijection between child natural zeros and the respective parent's strictly triangular zero slice. This is a stronger statement than existence of parent witnesses on the slice, but it is not a bijection with all original zeros. The graph restoration is a proof and API algorithm; no restored rank register is computed or needed by the emitted child polynomial, and no such gate is omitted from its evaluation cost.

## Fully paid literal ledger

The unchanged non-pointer local source has `33N` multiplications and `45N+3` additions, including the three root bindings. A row with `m=N-1-i` available forward targets pays

```
9m multiplications + 12*max(m,1) additions.
```

The products are the three field lookups in each of three slots. For `m>0`, each of the three active-slot sums and nine field sums pays `m-1` summation additions and its final subtraction. For `m=0`, these are still twelve paid `0-target` subtractions. No common-subexpression optimization or sign change of squared residuals is used.

Summing `m=0,...,N-1`, the comparison source has

```
M_certificate=(9N^2+57N)/2,
A_certificate=6N^2+39N+15.
```

Adding all `22N+3` residual squares and `22N+2` final additions gives the headline complete formulas. The supplied coordinates consist of 18 non-rank local fields per row and the `3N(N-1)/2` forward pointers, excluding the three external parameters. Removing the `N` rank rows leaves `22N+3` residuals.

The default `cleanup=False` simplifies only source nodes affected by the pointer substitution and prunes dead gates. The separate `cleanup=True` also removes the parent's preexisting `0+b` additions in the code constructor `F(0,b)`, exactly `N` more additions. These were charged by the original literal source and are reported separately. Neither schedule claims arithmetic optimality.

| N | Natural witnesses | Residuals | Selective operations | With static cleanup |
|---:|---:|---:|---:|---:|
| 1 | 18 | 25 | 142 | 141 |
| 2 | 39 | 47 | 285 | 283 |
| 3 | 63 | 69 | 449 | 446 |
| 4 | 90 | 91 | 634 | 630 |
| 5 | 120 | 113 | 840 | 835 |
| 6 | 153 | 135 | 1067 | 1061 |
| 7 | 189 | 157 | 1315 | 1308 |
| 8 | 228 | 179 | 1584 | 1576 |

The residuals remain quadratic. The retained `d_0-F(a_0,b_0)` has nonzero quadratic part `-(a_0+b_0)^2`, so the sum of the squared highest parts cannot vanish identically over the reals. The exact complete degree is therefore four for every `N`, including `N=1`.

The placed report's base compiler explicitly allows arbitrary row order and supplies heights. Its canonical refinement sorts nonroot input keys by numerical code rather than by topological order, and it additionally targets unique fibers. The checked source collection and existing eager Tree review contain no emitted triangular-pointer compiler. The present change uses the standard finite-DAG ordering fact; its contribution here is the exact source projection and paid finite ledger, not a new computability principle.

## API and reproducibility

`build` and `checked` reconstruct full canonical packets using exact integer `N` and exact Boolean `cleanup`. `evaluate` requires a complete natural assignment; `signed=True` permits integer polynomial evaluation only. `restore_flow` and `restore_height` return the complete parent assignments on the corresponding graphs. `project_triangular_zero` requires a parent flow zero already satisfying every forbidden-pointer condition. `normalize_parent_zero` accepts any parent flow natural zero and performs dummy replacement and root-first topological permutation. Each public build authenticates the parent and current kernel; no shared mutable packet cache is used.

The [receipt](eager_tree_triangular_projection.json) emits both complete schedules for `N=1,...,8`. Exact coefficient expansion proves 32 full polynomial graph identities to the two actual parent sources, 3,264 retained residual identities, and 144 identically vanishing restored rows. It also checks 128 signed whole-polynomial evaluations, 50 genuine application/padding normalizations, two disconnected-cycle normalizations, 33 malformed calls, and four independent copies. Two of the genuine cases specifically require a nontrivial row permutation. These bounded checks support the general proofs above rather than replace them.

Standard-library replay, without original suite reruns:

```sh
python eager_tree_triangular_projection.py --root /path/to/sibling/parent/files \
  --repo /path/to/Proofs --output /tmp/tree-triangular-replay.json \
  --expect eager_tree_triangular_projection.json
```
