# Generic sparse radix packing and digit extraction

For any finite list of natural position/coefficient pairs, `coefficientAt` sums all coefficients at a position, including duplicates. `sparse_sum` proves that, if every listed position is below `n`, the original weighted term sum equals the range-indexed sum of aggregated coefficients. `sparse_terms_digit` then proves that, for positive radix `b`, every aggregate below `b`, and `i < n`, dividing that weighted sum by `b^i` and reducing modulo `b` gives the aggregate at `i`. The companion range theorem connects the same sum to `Nat.ofDigits`; `finite_sum_lt` bounds it by `b^n` when `1 < b`. No uniqueness of list positions is assumed.

Bounded author-only session 27770 exited 0 with no warnings or `sorryAx`; exact named axiom reports are retained. Earlier successful stages, the failed sparse-sum attempt (whose `sorryAx` report is not evidence), and the subsequent warning-bearing success are preserved separately. The first source was reconstructed as disclosed in the observation. The output was checked against one package-only provider, whose transitive and dynamic ancestry is not independently authenticated.

These are generic natural-number results. No equality with `paramKernel`, a concrete coefficient, the retained bytes or display, no model cast, and no graph, converse or internal iPRA conclusion is claimed.
