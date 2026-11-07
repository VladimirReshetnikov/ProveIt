# 23-witness octic candidate by eliminating Delta

This external source-only candidate starts from the audited 24-witness octic seed. Its `Delta` residual is old coordinate 18 minus `(v16 + v15)^2 + 4*(v16 + v15) + 3`. Delete that residual and coordinate, substitute this polynomial throughout, and shift old coordinates 19–24 down one. Coordinate zero is preserved. The result contains 14 residuals and 23 witness coordinates. It keeps the same coefficient binding and resolves to the same files as its predecessor; `check.py` verifies both compressed and decompressed hashes.

The deleted coordinate reconstructs as a natural polynomial for natural witnesses. For a reverse lift/drop in an IΣ₁ model one must extract the old Delta residual, use injectivity of the natural embedding, and formalize the residual transfers and square-sum decomposition. The earlier sign24→25 q3 lift additionally requires an appropriate model-natural representation of beta; the sign25→26 pointwise seed-zero bridge and same-input existential equivalence are Lean-checked, while the sign25 endpoint and coefficient/model-port binding remain open. Sixteen finite natural controls are illustrations, not an all-model proof.

Each displayed residual has syntactic total degree at most four. Set new v16 = v17 = t and all other witnesses to zero, with integer ports fixed. The N0 residual is `-t^4 - 2*t^2 - 1`. Every residual has t-degree at most four, so the coefficient of `t^8` in the square-sum is the sum of squares of their t⁴ coefficients; N0 contributes one. Thus this coefficient is strictly positive for every fixed integer port valuation, and the external square-sum has exact total degree eight. Other residuals may contribute to t⁸, so uniqueness is not asserted.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/nine-sharing-sign23-octic-delta-candidate/build.py --check
python3 -I -S -B research/nine-sharing-sign23-octic-delta-candidate/check.py
```

The checker output matches `result.json`. This is a degree tradeoff, not a sextic or Lean degree theorem. No Lean bridge, iPRA endpoint, or nine-variable/Jones theorem is claimed. Independent audit requested.

The [independent candidate audit](../../reviews/nine-sharing-sign23-octic-delta-independent/README.md) passed for the substitution, natural reconstruction, fixed-port exact degree and stated model-scope limits.
