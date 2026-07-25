(*
  Assumption audit for the squared-square development.

  The only expected assumptions are the axioms of the classical real
  numbers from the Rocq standard library (the abstract completeness /
  classical-order interface of R).  No project-specific axioms are used.
*)

From SquaredSquare Require Import Defs Duijvestijn Intervals Minimality Scaling MinimalOrder.

Print Assumptions Duijvestijn.LeanProofs.SquaredSquare.exists_perfect_squared_square.
Print Assumptions Duijvestijn.LeanProofs.SquaredSquare.duijvestijn_perfect.
Print Assumptions Defs.LeanProofs.SquaredSquare.side_eq_of_congruent.
Print Assumptions Minimality.LeanProofs.SquaredSquare.seven_le_length.
Print Assumptions Scaling.LeanProofs.SquaredSquare.exists_perfect_squared_square_of_side.
Print Assumptions MinimalOrder.LeanProofs.SquaredSquare.minimal_order_21_iff.
