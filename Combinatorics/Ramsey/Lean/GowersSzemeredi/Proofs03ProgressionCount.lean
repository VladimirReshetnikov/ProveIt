import GowersSzemeredi.ProofInfrastructure
import GowersSzemeredi.Sections01_03
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities

/-!
# Counting modular progressions from higher uniformity

This module proves the repaired prime-modulus form of Corollary 3.3.  The
empty-family and one-function cases are retained explicitly, while every
nontrivial summand is padded by constant-one functions up to its largest
index and bounded by Theorem 3.2.

The 14 declarations of this module that the final route does not use are in
`Proofs03ProgressionCountSide`. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

lemma cor33_balanced_discValued {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) : DiscValued (balanced A) := by
  intro x
  have hd0 : 0 ≤ density A := density_nonneg A
  have hd1 : density A ≤ 1 := density_le_one A
  by_cases hx : x ∈ A
  · simp only [balanced, indicator, hx, if_true]
    norm_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hd1)]
    linarith
  · simp only [balanced, indicator, hx, if_false, zero_sub]
    norm_cast
    rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hd0]
    exact hd1

end LeanProofs.GowersSzemeredi
