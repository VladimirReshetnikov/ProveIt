# Symbolic K sparse-family exploration

These staged author-only modules prove `paramKernel r` equals the symbolic weighted sum of a 1,973-entry list and, equivalently, `Nat.ofDigits r` of the aggregated coefficients for every natural radix `r`. They prove every listed position is below 8850. No evaluation of K or retained bytes occurs. The family regrouping preserves every entry, including duplicate positions; no disjointness is assumed in the equality.

The digit extraction and overall upper bound are conditional on every aggregate coefficient being below `r`, plus the stated radix positivity or `1 < r`. That aggregate bound is not proved here. Exact successful compiler outputs, one failed Lean pattern attempt and one pre-compiler log-collision failure are retained in `observations/`; the failed attempt's `sorryAx` report is not evidence.

The source chain was checked in one fresh author overlay over the existing author-only finite-certificate provider and the foundation package. Direct provider hashes are post-run point-in-time observations; inherited transitive/package and dynamic ancestry is not independently authenticated. No paired build, retained `kernelNat`/bytes/display binding, model cast, graph consequence, converse or internal iPRA result is claimed.
