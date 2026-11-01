# Independent audit of the corrected 29-variable display

The corrected provisional PDF SHA-256 is `ecab3829b0f1c677945da5e6d3efdc099949766ce92be9a0e45c356e809056e7`. This audit checks all 135 printed circuit rows and 40 displayed definitions against the pinned graph, verifies the 20-square wiring, topology, liveness and mutation controls, and reproduces the PDF in two clean builds. A separate [alias audit](../equation8-29-30-alias-correction-audit/README.md) checks the corrected gate name and the rest of the explanatory aliases in both 29- and 30-variable presentations.

The scope check ties the candidate disclosure to the historical matched model receipt and failed native replay observation; it does not rebuild missing dependencies, rerun Lean, audit transitive provenance, or establish native equivalence. Earlier audit packets retain their original historical observations.
