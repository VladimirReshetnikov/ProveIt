# Independent source review: literal 74 factor residues

The main, direct-y auxiliary and strong factor patterns agree structurally
with the corresponding literal 74 graph fields, including all associations
needed for the proposed `rfl` proofs. The auxiliary ordinate is slot 11 and
its parameter f is slot 3; the strong argument is the graph's I field. The
review checker independently reconstructs the binary source DAG from all
literal rows and compares the three patterns.

The generic exclusions use `pairEval_residue` in the correct direction, and
the `main_bad`, `aux_bad`, and `strong_bad` argument orders match the cited
source theorems. The auxiliary rewrite is the exact identity
`y²−Q(y²−z²)=Qz²+(1−Q)y²`. Independent finite controls exhaust all 256 main,
256 auxiliary, and 64 strong residue assignments modulo four. The author
receipt reproduces.

From `Computability/DiophantineConsistency` run
`python3 -I -S -B reviews/ordinary14-74-factor-residues-independent/check.py | cmp - reviews/ordinary14-74-factor-residues-independent/observation.json`.
This is source and finite-arithmetic review only: the Lean proof and graph
are unelaborated. It does not establish the first or guard factor, positive
unit extraction, providers, model/iPRA endpoint or physical-byte/PDF binding.
No Lean run was performed.
