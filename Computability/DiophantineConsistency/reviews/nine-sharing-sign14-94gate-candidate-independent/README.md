# Independent external 94-gate candidate review

PASS. The checker reconstructs the prior 95-gate residual ASTs, independently replaces exactly five occurrences, and compares every resulting ordered subtree and row name to the pinned 94-gate candidate. Sparse polynomial normalization checks both the structural `t = h - 1` relationship and `t(t+2) = h² - 1`. Exact ordered-subtree hash-consing finds 85 live residual operations and 94 operations after the five squares and their sum: 37 additions, 17 subtractions and 40 multiplications.

The recorded upper bound depends on this explicit sharing convention and is not a minimality result. This audit is external Python evidence, not a Lean equivalence or a theorem about JSON, PDF or fixed-port files. The first independent checker invocation had a missing closing parenthesis and exited with a syntax error; this review records the corrected, passing checker.
