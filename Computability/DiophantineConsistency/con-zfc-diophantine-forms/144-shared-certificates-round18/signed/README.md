# Round18: signed spherical remainder bounds

New structural reduction: group eleven digit intervals into four Euclidean-ball bounds; optionally combine the two adjacent-exponent groups and replace one initial sign graph by an odd-square radix. The complete ordinary proof is `PROOF.md`. All variables range over unrestricted integers.

## Recommended achieved tradeoffs

| Endpoint | Variables | Quadratic rows | Quartic monomials | Height |
|---|---:|---:|---:|---:|
| sphere_dimension_centered_merged_odd | 258 | 186 | 5364 | 128446 |
| sphere_dimension_centered_odd | 259 | 185 | 5356 | 128446 |
| sphere_grouped_centered_merged_odd | 263 | 191 | 4141 | 128446 |
| sphere_grouped_centered_odd | 264 | 190 | 4135 | 128446 |
| sphere_sparse_centered_merged_odd | 285 | 213 | 3750 | 128446 |
| sphere_sparse_centered_odd | 286 | 212 | 3744 | 128446 |

The additional six baseline variants retain the old radix-output sign graph, isolating spherical batching from the optional odd-square refinement. Every endpoint folder contains the literal quadratic residual system, full collected quartic, source copies, exact metrics, and transformation certificate. All six displayed tradeoffs are achieved constructions, not global optimality claims.

## Reproduce

From this directory:

```
python build_spheres.py
python check_spheres.py
python -O check_spheres.py
```

No network or nonstandard Python package is needed. `source_inputs` contains the exact authenticated round17 inputs; `SOURCE_PINS.json` binds their bytes. Builder and independent checker share no code imports. The checker reconstructs untouched rows and all replacements in named coordinates, checks compacting and certificate metadata, expands every residual square independently, checks every metric, and rejects 30 malformed coefficient controls. `CHECK_NORMAL.json` and `CHECK_OPTIMIZED.json` record results. Arithmetic tests are illustrative finite controls, not the unbounded proof.

The released equation uses **D²−2Σr²**, with no unnecessary constant margin. Certificate polynomials use extended source indices (original input indices, optional odd-square root, then optional two scale wires); `retained_original_indices` gives the exact output compacting map.

Ordinary ZFC proves that each polynomial has an integer zero exactly when a finite ZFC refutation exists. Consequently its no-integer-zero assertion is equivalent to Con(ZFC). This is not a consistency proof and not a new end-to-end kernel-certified endpoint. The original calibrated source archive and its full mathematical/formal provenance remain part of the enclosing release; unchanged proof texts are copied in `inherited_proofs` for convenience.
