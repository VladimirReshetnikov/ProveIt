import Sharma2012.EndBlockConsequences
import Sharma2012.OppositeClassConsequences
import Sharma2012.ClassCountingConsequences

/-!
# Final upper-bound consequences for Sharma's paper

This module joins the reflected end-block theorems, the global class-size
argument, and the previously isolated finite-counting and analytic layers.
-/

set_option autoImplicit false

namespace LeanProofs.Sharma2012

/-- **Corollary 2.7.1.** Every odd/even interleaving class has cardinality at
most twenty, including the opposite endpoint orientation omitted by the
printed proof. -/
theorem corollary_2_7_1_holds : corollary_2_7_1 :=
  corollary_2_7_1_of_theorems theorem_2_6_holds theorem_2_7_holds

/-- **Theorem 2.8.** The recursive upper bound for `theta`. -/
theorem theorem_2_8_holds : theorem_2_8 :=
  theorem_2_8_of_corollary_2_7_1 corollary_2_7_1_holds

/-- **Theorem 2.9.** Sharma's exponential upper bound. -/
theorem theorem_2_9_holds : theorem_2_9 :=
  theorem_2_9_of_corollary_2_7_1 corollary_2_7_1_holds

/-- **Theorem 2.10.** The corresponding limit-superior bound. -/
theorem theorem_2_10_holds : theorem_2_10 :=
  theorem_2_10_of_corollary_2_7_1 corollary_2_7_1_holds

end LeanProofs.Sharma2012
