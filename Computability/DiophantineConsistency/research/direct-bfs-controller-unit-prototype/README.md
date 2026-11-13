# BFS-residue controller unit, conditional

`DirectBFSControllerUnit.lean` proves the controller Gamma residue and invertibility in every IΣ₁ model assuming that the model parameter `K` has the BFS remainder `264033855341` modulo `342946332593`. It imports the separately checked finite Gamma-order theorem and adapts the existing controller-unit argument to the new residue. The source also contains a natural-parameter version. This conditional theorem does not itself specialize to the enormous symbolic K, prove a calibrated rank, or establish iPRA provability.

Accepted author check `observations/directbfscontrollerunit-attempt02/`: Lean and outer runner exited 0 without diagnostics, with both enforced axiom reports limited to `propext`, `Classical.choice`, and `Quot.sound`. Object `/tmp/direct-bfs-controllerunit-adz3bl5j/DirectBFSControllerUnit.olean`, SHA-256 `1678575c029eeee7d6b6d8a5b5dd3bc08efb4c4b634f61fa48ff9663ff1e64c6`. Direct imports were pinned and rechecked; project, package-transitive, dynamic, and historical source-to-object ancestry remain inherited limitations. No independent Lean replay is claimed.

`observations/directbfscontrollerunit-attempt01/` and `run-attempt01.py` retain the original monolithic attempt, which exceeded Lean's 3 GiB interpreter limit. Attempt02 factors out the finite-order computation and symbolic specialization.
