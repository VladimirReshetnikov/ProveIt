# Focused research decisions

- Exact quadratic-part row dependence exposed three shifted syntax gates and
  the redundant affine factorial multiple. The selected shared gate is
  G=(2L+6)(2L+7); an initial pure-square chart had much larger coefficients
  and was not selected.
- Upstream158's two-coordinate fixed-base pool presupposes separate ordinary
  X and A*Y wires. The natural parent uses consecutive ordinates instead.
  A direct transcription creates the cubic term A*sum(Y^2); introducing U
  avoids this and gives a genuine three-coordinate pool. No impossibility
  claim is made about all two-coordinate natural encodings.
- A first unqualified predecessor assumption was rejected during ordinary
  proof review: deleting pow4 removes the only sign incidence for its seed.
  The final proof explicitly authenticates the ordinate using |X|, retains
  the other two orientations, and clears the possible inverse power by
  q^(y+1). The exact additive frame budget proves that the existing doubled
  lower frame is sufficient. This repair is in the final proof and checker,
  not left as an unchecked assumption.
- Residual-basis searches improve finite measured height/support after the
  dimension reduction. Their finite operation lists, not a heuristic
  optimizer run, define the selected outputs. The inverse shears and all
  coefficients are independently replayed; no search optimum is asserted.
