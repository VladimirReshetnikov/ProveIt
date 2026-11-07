# 24-witness octic candidate by eliminating q3

This external source-only candidate starts from the audited 25-witness octic seed. Its `q3` residual is old coordinate 15 minus `(beta * (v1 + 1) + 1)^3`. Delete that residual and coordinate 15, substitute the displayed cube for every occurrence, and shift old coordinates 16–25 down one. Coordinate zero is preserved. The result has 15 residuals in 24 witness coordinates. The candidate and predecessor resolve the inherited coefficient binding to the same files; `check.py` verifies both compressed and decompressed hashes and the nonzero beta bytes.

For nonnegative beta and natural inputs the deleted coordinate reconstructs as a natural cube. A reverse lift/drop requires the old zero's q3 equation and injectivity of the model's natural embedding. In nonstandard IΣ₁ models, representing the port beta by a model natural and establishing the lifted residual equalities and sum-of-squares decomposition are additional obligations. The byte checks do not bind the external coefficients to Lean ports. The coordinate correspondence is verified structurally, and 16 finite nonnegative-beta controls illustrate it; these controls are not an all-model proof.

Each residual has syntactic total degree at most four. Set new v16 = v17 = t and all other witnesses to zero, keeping ports fixed. The N0 residual is `-t^4 - 2*t^2 - 1`; all other residuals have t-degree at most two. Its square is the unique contributor to `t^8`, with coefficient one. Hence the external fixed-port integer square-sum has exact total degree eight. This is a degree tradeoff, not a sextic or Lean degree theorem.

Run from `Computability/DiophantineConsistency`:

```
python3 -I -S -B research/nine-sharing-sign24-octic-q3-candidate/build.py --check
python3 -I -S -B research/nine-sharing-sign24-octic-q3-candidate/check.py
```

The checker output matches `result.json`. No Lean syntax equivalence, zero-set bridge, iPRA endpoint, or nine-variable/Jones theorem is claimed. The inherited sign25→sign26 bridge is also still open. Independent audit requested.

The [independent candidate audit](../../reviews/nine-sharing-sign24-octic-q3-independent/README.md) passed for the substitution, external exact degree, coefficient hashes and stated conditional model scope.
