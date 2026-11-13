# Independent finite trace74 boundary probe

`check.py` independently evaluates the pinned 74-row candidate at the explicitly supplied arbitrary ports and ten positive trial coordinates using exact integers. It verifies the printed q, X, Y, k, c, rank and the first-index-two and main-index-three Pell identities, while `F+C=q` makes the proposed strict new-chart guard fail. The exact full graph output is nonzero; the independently computed signed-decimal output hash agrees with the author observation. The chosen beta=1 and MC=0 violate `0<MC<beta` for the fixed tuple.

This is a finite test of selected arithmetic constraints, not a trace74 graph zero, a counterexample to its guard, or a fixed-port result. It gives no conclusion about other choices of the unconstrained coordinates. This check evaluates the external candidate JSON, not a Lean-to-JSON binding; no Lean replay is involved.
