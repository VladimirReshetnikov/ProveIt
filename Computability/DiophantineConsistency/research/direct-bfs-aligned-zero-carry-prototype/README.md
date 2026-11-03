# Direct-BFS aligned and packed-word zero carry

`DirectBFSAlignedZeroCarry.lean` binds the direct-BFS stencil theorem to the actual temporal cyclic remainder of `(K + 2^(67e))*C`. For a bounded source with Boolean radix-2^67 digits, it proves every aligned source is Boolean and every cyclic carry vanishes. Its second theorem supplies those hypotheses for the direct-BFS packed word of arbitrary definable row and dummy functions. The result applies to every model of IΣ₁; it makes no local-word, phase, high-mask, halt, or iPRA assertion.

The accepted author run is `observations/directbfsalignedzero-attempt02/`: Lean and the outer runner exited 0, with no diagnostics and both captured axiom reports limited to `propext`, `Classical.choice`, and `Quot.sound`. Output: `/tmp/direct-bfs-alignedzero-_wtr0614/DirectBFSAlignedZeroCarry.olean`, SHA-256 `4f2d17e5356c545d92d5ae3a2de43182fd3474900e49c39e49dab33ced7ae0c9`. The runner checks all direct imports against first-resolved pinned objects before and after execution. This exploratory check inherits project, package, dynamic and historical source-to-object ancestry limitations and has not been independently replayed.

`observations/directbfsalignedzero-attempt01/` and `run-attempt01.py` preserve the failed namespace-opening attempt.
