# A 36-variable quartic with two factored root bindings

This candidate rewrites two residuals of the [36-variable combined-shift quartic](../adaptive-square-sums36-combined-shift-quartic/README.md) by distributivity. The positive-input straight-line graph has **36 variables, 153 operations and exact degree 4**, down from 155 operations at the same variable count and degree. The explicit nonnegative-input shift has 36 variables, 189 operations and degree 4. This packet establishes an exact external polynomial identity; the new graph has not been elaborated in Lean or given its own iPRA endpoint.

The two root-binding residuals are unchanged as integer polynomials:

```text
scale*firstQuotient - (scale*rootInner + Y*qm - w*cube)
  = scale*(firstQuotient-rootInner) - Y*qm + w*cube

mainScale*mainQuotient - (mainScale*offset + H*shift)
  = mainScale*(mainQuotient-offset) - H*shift.
```

Each factored expression uses one fewer binary operation. Both remain quadratic in the displayed inputs. No witness, domain, port or positivity assumption changes in this step. The checker verifies that **all 27 residuals** agree exactly with the parent over formal integer inputs and ports, and that both complete outputs are the same sum of their squares. Thus the output polynomials, and not merely their zero sets, agree for every integer valuation.

All 153 positive-domain operations, 36 positive inputs and four ports are live. The checker verifies all residual degrees are at most 2, while the coefficient of `firstQuotient^4` in the sum is 1; exact degree is therefore 4 for every fixed integer port tuple. The explicit natural shift adds 36 live `+1` gates and preserves degree.

The inherited 36→37 zero map requires represented nonnegative beta for its positive-product reconstruction; the fixed current-2011 beta satisfies that condition. The subsequent 37→38 and 38→40 maps and the historical 40-variable iPRA endpoint have their own stated review and provider limits. Although this final 155→153 step is an external exact identity for arbitrary ports, a Lean proof of that identity, the new zero-map chain, and the desired iPRA derivation remains open. The form strictly improves its 36/155/4 parent in operation count; it is not a global minimum.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums36-factored-roots/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums36-factored-roots/result.json
```
