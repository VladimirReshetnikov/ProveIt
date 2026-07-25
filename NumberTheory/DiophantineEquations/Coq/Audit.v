(* Kernel-assumption audit for the unconditional FLT-4 development. *)

From DiophantineEquations Require Import FermatFour.

Import LeanProofs.FermatFour.

Check Fermat42_odd_even_descent_step_holds.
Check Fermat42_mixed_parity_descent_step_holds.
Check Fermat42_descent_step_holds.
Check Fermat42_descent_statement_holds.
Check no_Fermat42.
Check fermat_four_no_square_right_int_solutions.
Check fermat_four_no_positive_nat_solutions.

Print Assumptions Fermat42_odd_even_descent_step_holds.
Print Assumptions no_Fermat42.
Print Assumptions fermat_four_no_square_right_int_solutions.
Print Assumptions fermat_four_no_positive_nat_solutions.
