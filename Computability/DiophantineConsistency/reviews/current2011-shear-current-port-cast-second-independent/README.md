# Independent source review: current2011 shear port/rank casts

No concrete mathematical or source-interface mismatch was found. The proposed model-natural tuple has exactly beta, K, lowPort and `highPort+beta`, matching the source `CurrentMasks2011.ports`; the final beta shift is included once. `currentP` is the cast of that same integer tuple, and the q/Y/c coordinates agree with `ArithmeticCarrierRadix2011` and `Carrier65.core` after the shared positive shift.

The rank comparison is conditional on `F≤q`: it is necessary because the natural model uses truncated subtraction while the difference-ring expression uses signed subtraction. The draft obtains that bound from its **unelaborated predecessor's** positive scalar gap and explicitly supplies the other bounds `1≤q` and `1≤q²` to the generic rank-cast source. The final theorem applies the predecessor's same-parent-zero cast transport. A bounded independent computation checks the index/tuple and all three subtraction differences under these hypotheses and exhibits a failure when `F≤q` is dropped. This numerical diagnostic is not a proof for arbitrary IΣ₁ models.

The current-port source and both predecessor snapshots remain unelaborated. `fin_cases`/`simp`, Nat/Int/model casts, `rw` ordering, the `q−1` normalization, the scalar-gap source, theorem-name resolution, potential large-port kernel reduction and provider compatibility all need actual Lean checking. The conclusion must not be treated as a verified graph bridge or endpoint. The parent zero premise, exact `highPort+beta` tuple and same valuation are essential; no positive-zero or consistency claim is made here.

The checker reproduces the author's static check and independently inspects the source shapes, port expressions and several hundred bounded arithmetic controls. From `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/current2011-shear-current-port-cast-second-independent/check.py | cmp - reviews/current2011-shear-current-port-cast-second-independent/receipt.json
```

No Lean/build/staging was performed. The author's source packet was not edited.
