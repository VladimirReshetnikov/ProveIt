# Projecting sparse lattice history wires

For the preferred row-selector compiler with an externally fixed initial configuration, horizon `T`, mass `M`, and supplied row count `S`, eliminate `T[7M+M(M−1)]` variables and the same number of defining residuals. The resulting natural certificate has

```
V = T[M(S+7)+4M(M−1)],
R = T[10M+4M(M−1)],
```

with quadratic residuals and a sum of squares of degree at most four. This is a reduction in witnesses and residuals for the [reviewed sparse-lattice family](review_sparse_lattice_aebfa386e.md). It does not give an unknown-duration fixed-arity equation or a measured arithmetic-gate reduction.

The [implementation](sparse_lattice_projection.py) transforms the actual emitted sparse polynomials. The [receipt](sparse_lattice_projection.json) records 48 complete instances, exact ledgers, restored natural tuples and decoded rows, 144 signed graph evaluations, 3,708 rejecting witness mutations, and six restricted-table/endpoint cases. The [independent review](review_sparse_projection_aebfa.md) checks the defining equations and their actual consumers with a separately implemented sparse polynomial algebra and full symbolic SOS expansions. Root reproduces its 542-check receipt. Finite checks supplement the argument below.

## Projection and natural restoration

Delete seven wires per particle and layer: its streamed position, three incoming masses, and three output masses. Replace each by the right side of its monic defining equation. For each of the `M(M−1)/2` sorting comparators, additionally delete the `xmax` and `zmax` wires, replacing them by `x+y−xmin` and `z+w−zmin`. Keep both min wires, every comparison flag/slack, and every channel/table selector.

The streamed positions and sorted row coordinates remain affine expressions, even after repeated substitutions: the retained min wires stop quadratic comparator expressions from expanding into later comparisons. Output masses are affine selector sums. Incoming masses become quadratic equality-flag times channel-selector sums and occur only linearly in the table-input moment equations. Thus no retained residual exceeds degree two. Every discarded defining row becomes the zero polynomial under the complete restoration map; consequently the entire original sum of squares, restricted to this graph, equals the new sum of squares on **all integer tuples**, including tuples with negative coordinates.

Natural restoration requires its own proof. Induct on complete layers. From a valid preceding row, the light-cone shift implies streamed positions are nonnegative. Forced comparison bits then give exact collision equalities, so the incoming sums are nonnegative. The natural selector simplex forces one actual row and nonnegative output masses. The rank comparisons give genuine channels. At each sort comparator, its forced bit and retained min equations make the deleted max expression the other nonnegative input. The resulting row is exactly the next canonical physical row. This restores every removed variable as a natural integer at every new natural zero, not only at the compiler-generated witness.

Conversely every old natural zero satisfies the substituted rows after dropping the selected coordinates. Restoration and projection are inverse on zeros; the uniqueness and endpoint semantics of the original compiler therefore survive. Naturality of intermediate position and max expressions is not claimed for arbitrary new natural tuples away from zeros.

Each eliminated wire had exactly one affine or quadratic defining residual. There are `7M+M(M−1)` deletions per layer. Subtracting them from the original `M(S+14)+5M(M−1)` variables and `17M+5M(M−1)` rows gives the displayed ledger. The orthant-exact backend adds its original `2MT` norm rows; prescribed endpoint rows remain separately paid. Restricted tables retain their original coverage contract. These counts do not apply to the factorized lookup backend or silently include a uniform loader/observer.

Affine substitution can lengthen sparse expressions and repeat work. The implementation records before/after term counts, but neither those counts nor the witness reduction proves a better straight-line schedule. A future optimized evaluator must explicitly share restored expressions and pay its complete source and finalizer.

```
python sparse_lattice_projection.py \
  --archive /path/to/Sparse_Lattice_Diophantine_Certificates.zip \
  --expect sparse_lattice_projection.json
```

The helper imports only a hash-pinned producer extracted privately from the pinned original archive. It does not change the report or its original fixtures.
