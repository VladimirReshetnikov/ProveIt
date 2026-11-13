# Actual 72-zero main index and large-c bound

[`FreeMainActualLarge.main_index_large`](FreeMainActualLarge.lean) passed the
[guarded Lean check](observations/attempt02/result.json). In every `IΣ₁`
model, for any natural ports and actual positive 72-graph zero with `q≥33`,
it supplies the natural-model main root `g` and Pell index `m`, their norm,
carrier and coordinate equations, and proves

```
6 ≤ m,      (a+2) * delta(a)² < c.
```

The client combines the checked actual main-root/index theorem, the checked
generic free-carrier lower bound, and the existing `large_of_six` theorem.
The index and root are elements of the possibly nonstandard model; no
standardness claim is made. The source comment “unchecked draft” predates the
successful check and is retained to match the receipt.

Lean exited 0 with `[propext, Classical.choice, Quot.sound]`, no warnings or
`sorryAx`, stable direct-input guards and no monitor stop. Object SHA-256:
`47d2c20249e9cadd6e985df44786e8626af091f99c3091f1746845f6fe112c0b`.
The [first attempt](observations/attempt01/result.json) failed only on an
association mismatch and is preserved with its source and log. Direct-provider
guards inherit transitive, dynamic and between-sample ancestry.

This result supplies the large-c premise needed by the signed half-index
argument when the other hypotheses are available. It does not itself establish
those other residual/window hypotheses, identify `m=R`, prove the 72→76
reverse implication, or provide an iPRA endpoint. In particular, `q≥33` is a
hypothesis here; specializing it to the fixed compact44 ports is separate.
