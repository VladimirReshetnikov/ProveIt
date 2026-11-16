# Suggested ProveIt integration

Suggested destination:

```text
Logic/PrimitiveRecursiveArithmetic/docs/proofs/analysis/
  lagrange_inversion_ipra_2026-11-15/
```

The packet can initially be committed unchanged. For a kernel-checked Lean
completion, move or copy the Lean sources into an appropriate library source
directory and add a `lean_lib` root only if the existing `ProveIt` library root
does not already cover the path.

## Recommended order of formalization

1. `TruncatedSeries.lean` and `FixedPoint.lean`.
2. `FormalResidue.lean` and the denominator-free alternative formula.
3. The cleared derivative formula and inverse specializations.
4. Bell polynomials and finite applications.
5. Natural-number encodings and the object-theory `Prf PRAAx [] phi`.
6. Transport with `pra_theorem_iff`.
7. Multivariate, Puiseux, and analytic-lifting modules.

The completion criterion is replacement of the two `opaque` declarations in
`lean/LagrangeInversionBlueprint.lean` by an explicit iPRA proof object and its
transport. Meta-level Mathlib equality alone is not the final object-theory
result.

## Local checks

From the packet root:

```bash
./build.sh
python3 code/verify.py
sha256sum -c MANIFEST.sha256
```
