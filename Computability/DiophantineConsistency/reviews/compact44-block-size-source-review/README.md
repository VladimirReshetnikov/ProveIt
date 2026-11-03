# Independent source review of compact block-size proofs

The review covers these exact checked source files:

* [`CompactKernelBlockSize.lean`](../../research/ordinary12-ipra-bridge/compact44-kernel-split-prototype/CompactKernelBlockSize.lean),
  SHA-256 `7250db9d9c4f4202fc2e14b855499744e167338673db616b5be13ee805fdb1cb`;
* [`CompactMarkedCellSum.lean`](../../research/ordinary12-ipra-bridge/compact44-marked-cell-sum-prototype/CompactMarkedCellSum.lean),
  SHA-256 `b40cab70269e492f8bfc94d7d4766a58861195c3a4df7aa70be35cf4157d2b11`.

For `CompactKernelBlockSize`, the reviewer checked the explicit model
hypotheses and arithmetic chain. In a model of IΣ₁, if
`x < 2^(67*3297+1)`, the exact symbolic-kernel split and the previously
proved low-product bound imply that the high half of `K*x` is
`2^(67*42)*x`. For `cell_sum_of_small`, the assumptions are `0 < N` and
that bound for every `X j` with `j < N`. Positivity of `N` puts the two
cyclic predecessor indices in range. The proof bounds the cell, low product,
high product and temporal predecessor by a common exponent, adds the four
bounds, and compares their sum with `2^590069`. No definability assumption
on `X`, stride restriction, or high-mask assertion is needed for this
pointwise size theorem.

For `CompactMarkedCellSum`, the assumptions are `CompactWord row N s` and
`δ j ≤ 1` for every `j < N`. The word provides `N > 0` and excludes row 1
at valid indices. The pulse bound is proved by splitting each Boolean value
into zero or one; the generic block-size theorem then supplies both the
base and pulsed cell-plus-block bounds. The theorem does not require pulse
support or function definability. Neither source proves high-mask no-carry,
the full `PackingInput`, a graph zero, retained-byte binding, or an internal
iPRA derivation. No mathematical defect was found in the reviewed theorem
statements or these proof steps.

At review time, the two workspace source hashes matched their respective
author receipts. The block-size object and log hashes matched the receipt
at `188c5933650d77ab914b4fc018f038707cc0ea3a8d38f835a021b6a22927d6cc`
and `647dae9d08cce4292deec392ac3a1cf79f9a97c0809e60825a792a6ed2224a58`;
the marked-cell object and log hashes matched at
`cc9836dcc6d4bdc6984ce7a7b1fe2acb76161f9401e5b875b689a4e0273cc75e`
and `5a365c0c2e9dc1104a87d51e205a5ae410a306b2f82ec44d6d7c7ea3c4d59521`.
The respective receipts report exit 0 and unchanged selected direct and
overlay guards. This is an independent **source and point-in-time artifact
inspection**, not an independent Lean compilation, paired replay, or
authentication of the inherited package, transitive, dynamic-loading or
between-observation ancestry.
