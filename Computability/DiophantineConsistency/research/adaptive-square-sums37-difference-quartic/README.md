# A 37-variable quartic from one positive square difference

This external candidate reduces the [38-variable positive quartic](../adaptive-square-sums38-two-quadratic-products/README.md) to **37 positive variables, 158 operations and exact degree 4**. Its explicit nonnegative-input shift has 37 variables, 195 operations and degree 4. The graph, identities and degree have exact finite checks; the zero maps below are mathematical arguments, **not yet Lean derivations**. No physical TeX/PDF or iPRA endpoint for this new graph is asserted.

The 38-variable graph uses separate positive inputs for `squareVariable = vValueVariable²` and `ySquareVariable = y²`. Replace both with one positive input `differencePlusOne`, representing

```text
differencePlusOne = y² - vValueVariable² + 1.
```

The child enforces this relation with one squared quadratic residual. It rewrites the auxiliary factor to `y² - qValueVariable*(differencePlusOne-1)`. All other residuals are retained, and the old two square-definition constraints disappear. Reusing one constraint position and removing the other, while introducing one subtraction gate, changes the counts from 38/160/29 to 37/158/28 for variables, operations and squared residuals.

## Why the new positive witness exists

Let `Q` denote the positive input `qValueVariable`, and let `v` denote `vValueVariable`. At any **positive parent zero**, every squared residual vanishes. The two square constraints give the values `y²` and `v²`, and the auxiliary residual gives

```text
Q*(y²-v²) = y²-1.
```

Because `y≥1` and `Q>0`, the right side is nonnegative and the difference `y²-v²` is nonnegative. Thus `differencePlusOne` as defined above is at least 1. Project the other 36 inputs unchanged and use this positive value for the new child input. The new relation and all child residuals vanish.

Conversely, at a **positive child zero**, all 28 squared residuals vanish, including `differencePlusOne-1 = y²-v²`. Restore the two parent inputs as `squareVariable=v²` and `ySquareVariable=y²`; they are strictly positive because the retained `v` and `y` are positive. The removed parent residuals vanish, and the surviving residuals vanish. The exact identity checked for the only nonidentical residual is

```text
parentAux = childAux + Q * differenceEquality,
differenceEquality = (differencePlusOne-1) - (y²-v²).
```

These maps are inverse on zeros. The parent and child outputs need **not** be identical away from zero, so this is a zero-set equivalence rather than a polynomial identity.

The same order argument applies mathematically in every model of IΣ₁ used by the parent bridge. In its difference ring, positivity of the embedded `Q` reflects the sign of a product. Since `y≥1`, the auxiliary equality gives nonnegative embedded `y²-v²`; the embedding reflects order and the natural-model order supplies `d` with `y²=v²+d`. Taking `differencePlusOne=d+1` is positive. This uses the model's ordered semiring and difference-ring facts, not standard-natural prime factorization or a sign choice for the Pell roots. Its Lean formalization, instance resolution and iPRA proof-existence transfer remain separate and unverified.

The read-only checker pins the 38 parent and both 37 DAGs, verifies every row edit and all liveness and count claims, checks both outputs are exactly their listed sums of squares, and proves the residual identities as exact sparse integer polynomials over formal port parameters. Each child residual has degree at most 2; `firstQuotient^4` has coefficient 1 in the output, so degree is exactly 4 for every fixed integer port tuple. The natural shift preserves this degree. It does not execute Lean, establish the model proof or authenticate a transitive provider closure.

The earlier 40-variable parent is row-matched to `AdaptiveQM40Context.literal`; its native and standard iPRA endpoints have historical author-side compilation with their documented provenance limitations. Combining those retained results with the external 38 and 37 zero maps gives an external equivalence conditional on the inherited parent results. Establishing the **new** internal iPRA statement needs checked Lean model maps and endpoint composition. This form strictly improves the positive 38/160/4 parent in variable and operation counts, while trading more variables and operations for lower degree compared with the specified 13- and 14-variable candidates. It is not a global minimum; separate 37-variable quartic proposals use different domains and constructions.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums37-difference-quartic/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums37-difference-quartic/result.json
```
