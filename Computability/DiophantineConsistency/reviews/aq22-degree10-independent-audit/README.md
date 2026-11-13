# Independent audit of the AQ22 graph

This finite audit independently checks the graph in
`../../research/adaptive-square-sums22-degree10/` against its AQ26 parent.
`audit.py` pins both input graph hashes and implements a separate sparse
integer-polynomial evaluator. It extracts the squared residuals from the
actual output graphs, verifies their 17-to-13 correspondence after all four
substitutions simultaneously, and checks each deleted residual becomes zero.
It also verifies child topology, liveness, and positivity-relevant wiring.

For the 13 residuals it computes degree in the 22 witness coordinates while
retaining the four fixed ports as symbolic variables. The maximum is five;
the coefficient of `f^2*y^2*deltaVariable` in `auxResidual` is exactly −1,
with no port dependence. Consequently the square sum has degree exactly ten
after any real specialization of the ports: its degree-ten homogeneous part
is a sum of squares containing a nonzero summand. This is not a claim of
minimum degree or minimum coordinate count among other constructions.

For the ordinary integer witness transport, three reconstructed coordinates
are directly positive when the retained witness inputs are positive and
`beta >= 0`. The fourth, `QComputed`, is positive at a child zero because the
retained `g72` residual makes it equal `(cSquareVariable*i)^2`. A zero of
the sum of squares makes every residual zero; conversely, the four parent
binding residuals give the expressions on projection. This reasoning is not
a Lean-checked witness transport, an iPRA derivation, or a proof of the
equivalence with `Con(ZFC)`.

Run from the repository root with ordinary Python:

```sh
python3 Computability/DiophantineConsistency/reviews/aq22-degree10-independent-audit/audit.py
python3 Computability/DiophantineConsistency/reviews/aq22-degree10-independent-audit/mutation_controls.py
```

The first command writes `receipt.json` and refuses to overwrite an existing
receipt; remove a copied receipt before rerunning. In the recorded run it
exited zero and produced the checked-in receipt. The second command exited
zero after verifying that a reversed `g72` sign and a changed retained `Fa`
row are rejected even when the child hash pin is updated, and that Python
`-O` and `-OO` are refused. Mutation runs use temporary copies and leave the
original graphs untouched.
