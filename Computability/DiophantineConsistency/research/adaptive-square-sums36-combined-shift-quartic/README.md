# A 36-variable quartic from a combined positive shift

This source-only candidate reduces the [37-variable positive quartic](../adaptive-square-sums37-difference-quartic/README.md) to **36 positive variables, 155 operations and exact degree 4**. The explicit nonnegative-input shift has 36 variables, 191 operations and degree 4. The checked zero maps require the beta port to be nonnegative, as it is for the fixed current-2011 ports. The new graph and its model maps have not been elaborated in Lean and do not yet establish a new internal iPRA derivation.

In the positive 37-variable parent, the two positive inputs `productVariable` and `gammaProductVariable` are constrained by separate squared residuals to be

```text
productVariable      = productVariable2 * q
gammaProductVariable = mainScaleVariable * gamma
q                    = 1 + J*beta.
```

Their only other uses are together in the sum feeding the main-root shift. Replace them by one positive input `combinedShift`, impose one squared quadratic residual

```text
combinedEquality = combinedShift
                  - (productVariable2*q + mainScaleVariable*gamma),
```

and use `combinedShift` directly in the shift. This removes one input and one squared residual; removing the original sum gate and the second constraint while adding the new computed sum changes 158 operations to 155. All 155 graph rows, all inputs and all ports are live.

At a positive parent zero, both old product constraints vanish. Set the new input to the sum of the two old positive inputs; it is positive, the new residual vanishes, and all child residuals vanish. Conversely, at a positive child zero, the combined residual vanishes. Restore the old inputs as the two displayed products. The gamma product is positive; the other is positive whenever `q>0`. It is enough that `beta≥0`, since the retained inputs are positive and `q=1+J*beta≥1`. Under these reconstructions the removed parent constraints vanish, all unchanged residuals agree, and the remaining changed residual satisfies the exact identity

```text
parent dDifference = child dDifference + H*combinedEquality.
```

Thus both maps preserve zeros and are inverse on zeros. The parent and child output polynomials are not claimed equal off the combined constraint. Other ports may be arbitrary integers for this local argument. The assumption on beta is sufficient; no claim is made here about negative-beta cases.

The fixed historical 40-variable endpoint uses `CurrentWindowCarry2011.ports`. The pinned source defines its first port as the natural number `beta=(2^47)^2011-1` and states its positivity theorem; hence the beta condition holds for the intended standard integer tuple. In an IΣ₁ model, using its represented natural beta gives `q≥1` and the same ordered-semiring positivity argument. This is a mathematical model explanation, not a checked Lean proof of the new transfer.

The checker pins both DAGs and the current beta source, checks every graph edit, liveness and operation count, proves exact sparse-polynomial residual identities with formal port parameters, and checks both outputs are their claimed sums of squares. Every child residual has degree at most 2; `firstQuotient^4` has coefficient 1, so exact degree is 4 at every integer port specialization. The positive shift preserves the degree. The checker does not parse or run Lean, establish the model transfer, authenticate provider ancestry, or bind document bytes.

Composing this external zero map with the separately checked 37→38 map and independently reviewed 38→40 map gives an external equivalence conditional on the retained historical 40-variable endpoint and its stated provenance limitations. The independent review of the 37→38 map is still pending. The **36-variable internal iPRA endpoint remains open** pending checked Lean maps and composition. This strictly improves the 37/158/4 positive parent in variables and operations; compared with the specified 13- and 14-variable forms it trades more variables and operations for degree 4. No global minimality or unrestricted-integer-domain claim is made.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums36-combined-shift-quartic/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums36-combined-shift-quartic/result.json
```
