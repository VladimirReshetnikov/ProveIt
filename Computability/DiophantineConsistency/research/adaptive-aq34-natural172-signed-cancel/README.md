# A 34-variable natural-domain graph with canceled signed shifts

The existing [34-variable, 144-operation, degree-6 positive-domain candidate](../adaptive-square-sums34/README.md) has a historically matched native iPRA endpoint for its `positiveShift` expression. Writing that shift as a shared straight-line program would add 34 `+1` operations. This packet cancels six of those operations in three signed differences, yielding a **34-nonnegative-variable, 172-operation, exact-degree-6 graph**. Its output is exactly the positive-shifted parent polynomial for every integer input and every integer port tuple; it is not merely a claimed zero-set equivalence.

The six parent coordinates appear nowhere except in the indicated three differences:

```text
namedBt = wPositive - wNegative
Dstar  = dPositive - dNegative
V      = vPositive - vNegative.
```

After the ordinary positive shift, each becomes `(u+1) - (v+1) = u-v`. The candidate uses the two nonnegative inputs directly in each of these three rows and keeps the `+1` gate for each other input. The exact checker confirms the six exclusive uses, every parent-to-child row, all 172 operations and all inputs and ports are live. This is a syntactic cost improvement for the **natural-domain** straight-line evaluator, not a reduction of the parent's 144-operation positive-domain evaluator.

The checker also compares the parent JSON's 34 inputs, four ports and all 144 rows directly to the pinned `AdaptiveAQ34Literal.literal` Lean source. It checks the candidate output is exactly the sum of the same 22 squared residuals; all residuals have degree at most 3, and the first has a port-independent cubic monomial with coefficient `-1`. The sum of squares therefore has exact degree 6 for every integer port tuple. The candidate graph and proof are external certificates; a Lean proof that its literal and `positiveShift` have identical evaluation, followed by an iPRA endpoint client for the new syntax, has **not** been produced here.

`IPRAAQ34Native.literal_equivalence` states the retained native-iPRA endpoint for the parent at `CurrentWindowCarry2011.ports`. Its [historical focused replay](../../reviews/adaptive-aq34-native-replay/README.md) matched with the documented inherited provider ancestry. An exact external row comparison and affine identity do not authenticate a new compiled object, close that ancestry, or establish document/PDF semantics. The separately retained matched-endpoint 31/141/6 positive graph has a straightforward 31/172/6 natural shift and therefore dominates this candidate on variable count at the same displayed gate count and degree. This packet is useful as an exact syntax/endpoint comparison, not as a frontier improvement. No global minimum is claimed.

From the repository root:

```sh
python3 -I -S -B Computability/DiophantineConsistency/research/adaptive-aq34-natural172-signed-cancel/check.py | cmp - Computability/DiophantineConsistency/research/adaptive-aq34-natural172-signed-cancel/result.json
```
