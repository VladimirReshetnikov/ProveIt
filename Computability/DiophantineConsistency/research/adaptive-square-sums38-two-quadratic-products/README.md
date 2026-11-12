# A 38-variable quartic by eliminating two quadratic names

This candidate reduces the existing 40-positive-variable, 166-operation quartic to **38 positive variables, 160 operations and exact degree 4**. It is a rigorously checked external zero-set transformation, not yet a Lean theorem that the new graph has the inherited iPRA equivalence. The nonnegative-input graph is supplied separately: it substitutes each positive input by a nonnegative input plus one, giving 38 nonnegative variables, 198 operations in the displayed straight-line program, and degree 4.

In the [40-variable parent](../adaptive-square-sums40-quotient-quartic/README.md), two positive inputs are named products with their own squared constraints:

```text
ellProductVariable = ellVariable * (ellVariable + eta + zeta)
deltaProductVariable = deltaVariable * cSquareVariable.
```

Each name's only other use is inside a first- or main-norm residual, respectively. Substitute the quadratic right side directly into that residual and remove the corresponding defining squared constraint. The first- and main-norm residuals remain quadratic. The other 27 surviving residuals remain identical under the substitution. Removing two difference nodes, two squaring nodes and two additions takes the positive straight-line count from 166 to 160; all remaining operations, inputs and ports are live.

For any integer port tuple and any positive child inputs, lift to a parent tuple by inserting the two displayed products. Both products are **strictly positive**, since `ellVariable`, `eta`, `zeta`, `deltaVariable` and `cSquareVariable` are retained positive inputs. All 29 surviving residuals agree exactly and the two removed residuals vanish, so the entire parent and child outputs agree. Conversely, a positive parent zero has every squared residual equal to zero, forcing exactly these two products; projecting them out gives a child zero. The maps are inverse on zeros. No calibration or sign assumption on the four integer ports is needed for this local map.

The checker proves the source relations as finite exact polynomial identities with four formal port parameters. It separately verifies that both outputs are the claimed sums of squares, the child has 29 residuals of degree at most 2, and `firstQuotient^4` has coefficient 1 in the child output. Hence its exact degree is 4 for **every** integer specialization of the ports. The 38-input positive shift preserves degree, and the explicit natural-input DAG adds one operation per input. The checker also scans each of the 23 remaining directly defined auxiliary inputs individually, under the fixed original residual presentation and formal ports: substituting its existing defining expression makes at least one other surviving residual exceed degree 2. This is not a proof against a different refactoring, simultaneous elimination or a specialized-port cancellation.

The parent JSON is checked row for row against `AdaptiveQM40Context.literal`. The historical [native author run](../../reviews/adaptive-qm40-native-incremental-author/README.md) and [standard author extension](../ipra-standard-qm40/author-rebuild/README.md) report the positive-shifted 40-variable endpoint with the selected Foundation ZFC refutation and translated consistency targets. They are single-author incremental results with the documented inherited provider and transitive-ancestry limitations. The new 38-variable graph has **not** been elaborated in Lean, and the positive-witness/zero-map equivalence has not been internalized or composed with that endpoint. The local external zero maps support an external consistency-equivalence claim conditional on the retained parent results; they do not independently establish the desired new iPRA derivation, authenticate PDF semantics, or prove minimality.

Among the specified 13/86/99, 13/95/28, 13/94/50 and 14/79/107 forms, this is a tradeoff: the new form has a lower degree and more variables and operations. It strictly improves the 40/166/4 parent in variable and operation count under the same positive-domain metric. The repository also contains separately scoped 37-integer quartic proposals; domain, construction and proof status must be compared before asserting any broader frontier.

Reproduce from the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-square-sums38-two-quadratic-products/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-square-sums38-two-quadratic-products/result.json
```
