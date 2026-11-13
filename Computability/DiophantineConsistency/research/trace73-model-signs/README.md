# Conditional 73/75 transfer via sign bounds

`from75_of_bounds` takes a positive 75-zero and assumes, in the model difference ring, `0 ≤ V² B < ι(n)`. It constructs a positive 73-zero by obtaining a model-natural representative of the shift and subtracting it from `n`. `from73_of_nonneg` takes a positive 73-zero and assumes `0 ≤ V² B`; it constructs a positive 75-zero. Both use the same port and valuation registers as the checked literal-row substitution. `shift_nonneg_of_B` shows the shift is nonnegative whenever `B ≥ 0`.

These are conditional statements: no sign or strict center bound is established for arbitrary graph zeros, and no unconditional equivalence or iPRA statement for the 73 graph is claimed. In particular, the 75-side strict bound and the 73-side sign are separate obligations.

The guarded Lean author run `observations/attempt01/` and its outer runner exited 0; diagnostics were empty apart from three axiom reports. The output `/tmp/trace73-signs-7edju0w1/Trace73ModelSigns.olean` has SHA-256 `fc3a5776eb50bccdb99874e90fd09242432a6540dc4156ac5d30bd3a98b440f9`. The direct imported transfer object is pinned; the earlier literal-to-JSON check is external, and project/package/dynamic ancestry remains inherited.
