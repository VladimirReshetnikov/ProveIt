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

The following comparisons use `(variables, operations, degree)` and distinguish positive-domain graphs from natural-domain graphs. They refer to specific retained constructions, not a claimed exhaustive or provenance-independent frontier:

| Retained construction | Positive graph | Straightforward natural shift | Scope |
| --- | --- | --- | --- |
| [AQ30](../adaptive-square-sums30-degree8/) | 30/138/8 | 30/168/8 | Historical matched native endpoint for the shifted parent, with its documented provider limits. |
| [AQ31](../adaptive-square-sums31-degree6/) | 31/141/6 | 31/172/6 | Lower degree; does not dominate 33/164/8 on operations. |
| [AQ27](../adaptive-square-sums27-degree8/) | 27/129/8 | 27/156/8 | Numerically dominates 33/164/8; author-side historical hybrid endpoint provenance. |
| [AQ26](../adaptive-square-sums26-degree8/) | 26/126/8 | 26/152/8 | Numerically dominates 33/164/8; author-side historical hybrid endpoint provenance. |
| [Two-quotient AQ26 reduction](../adaptive-aq26-two-quotients122/) | 26/122/8 | 26/148/8 | Numerically dominates 33/164/8; new expression's Lean transfer and iPRA endpoint remain open. |

The broader local inventory also examined the retained AQ28–30 degree-eight and AQ31–33 degree-six graphs, and separate ordinary 13- and 14-input constructions. The latter include degree-28 and higher constructions with different port encodings or proof status; they do not dominate this graph at degree at most eight merely by having fewer variables. A structural-degree scan of JSON graph files is described in the [inventory](../adaptive-aq26-comparison-inventory/README.md); other formats and constructions are outside that finite scan. Neither these comparisons nor the scan establish global optimality. The 33 candidate's exact equality to a historical matched-parent expression remains a distinct provenance benefit; the new 26/122 candidate's external zero-map does not imply a compiled Lean endpoint.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-named33-natural164-signed-cancel/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-named33-natural164-signed-cancel/result.json
```
