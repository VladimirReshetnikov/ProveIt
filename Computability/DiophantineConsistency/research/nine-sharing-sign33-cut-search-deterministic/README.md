# Deterministic bounded conditional signed-cut search

This fresh revision sorts the baseline cut names before seeded mutations and pruning. The earlier [search packet](../nine-sharing-sign33-cut-search/) remains preserved with its independently discovered hash-order reproducibility failure. Two separate author processes running `python3 -I -S -B search.py` produced byte-identical output, exit 0. The search seed is 20261106 and the run has 6,000 iterations.

The best examined result has 19 cuts plus 14 shifted inputs, again **33 witnesses**; no below-33 reduction was found. The search only considers degree-two residual propagation with the specified cut sign orientation, keeps `qm/q` inline and `q2` materialized for normalization, and is neither exhaustive nor a lower bound. The alternate 33-cut selection has no generated residual AST or checked forward sign proof. No new endpoint follows.

Source SHA-256 `9db5e41a3f033f5d82e2edcdeffcc3aadf85962c5ee3e748c9e22e01450caa01`; result SHA-256 `758119caebe99ae98776787ef82c991942c744790b765a2849620c2e6574107d`. Independent reproducibility and scope review required.

The [independent search audit](../../reviews/nine-sharing-sign33-cut-search-deterministic-frontier-independent/) passed, including two fresh isolated replay comparisons. The search remains restricted and non-exhaustive; no lower bound follows.
