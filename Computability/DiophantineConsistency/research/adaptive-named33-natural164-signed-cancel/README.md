# A 33-variable natural graph with four canceled signed shifts

The retained [33-variable, 139-operation, degree-8 positive-domain graph](../adaptive-square-sums33/README.md) has a historically matched native iPRA endpoint for its `positiveShift` expression. Expanding that shift as a shared graph adds 33 `+1` gates. Four exclusively used signed pairs cancel those additions, giving a **33-nonnegative-variable, 164-operation, exact-degree-8 graph** whose output is exactly the positive-shifted parent polynomial for every integer input and port tuple.

Each pair of positive inputs appears only in its indicated difference:

```text
namedBt = wPositive - wNegative
Z       = zPositive - zNegative
Dstar   = dPositive - dNegative
V       = vPositive - vNegative.
```

After positive shifting, `(u+1)-(v+1)=u-v` allows both additions for each pair to disappear. The other 25 inputs retain their individual `+1` gates. The checker confirms each exclusive use, every source-to-candidate graph row, and liveness of all 164 operations, 33 natural inputs and four ports. This is a natural-domain straight-line cost reduction, not a reduction of the parent's 139-operation positive-domain evaluator.

The same check matches the parent JSON's 33 inputs, four ports and all 139 rows directly to the pinned `AdaptiveNamedValues33.literal` Lean source. It verifies the output is the sum of the same 20 squared residuals. All residuals have degree at most 4, and the first has a port-independent degree-4 monomial with coefficient `-1`; the sum of squares has exact degree 8 for every integer specialization of the ports. These are exact external source/polynomial checks, not a new Lean proof about the candidate syntax.

The parent's `IPRANamedValues33Native.literal_equivalence` is recorded by a [historical matched native replay](../../reviews/ipra-named33-native-verification/README.md), with its stated inherited project, package and dynamic-ancestry limitations. A Lean proof binding the new 164-gate literal to that positive-shifted parent, followed by a new iPRA endpoint client, remains open. No document/PDF semantics or global minimality is asserted.

The existing matched-endpoint 30/138/8 positive graph has a straightforward 30/168/8 natural shift, while the retained 31/141/6 positive graph shifts to 31/172/6. This 33/164/8 natural form trades more variables for fewer operations than those straightforward natural evaluators. However, the separately retained 27/129/8 positive candidate has a straightforward 27/156/8 natural shift, which numerically dominates 33/164/8; its associated AQ27 endpoint has author-only hybrid provenance rather than the 33 parent's matched native replay. This packet is therefore a provenance-specific comparison, not a numerical frontier or global minimum.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-named33-natural164-signed-cancel/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-named33-natural164-signed-cancel/result.json
```
