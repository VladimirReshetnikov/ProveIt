import GowersSzemeredi.Proofs18RelativeProgressionCount
import GowersSzemeredi.Proofs18GeneralRelativeCount

/-! Integer-valued four-term counts and the relative-uniform stopping rule.
Constant progressions are included in the count and explicitly removed. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- Count all four-term progressions, including zero common difference. -/
def fourTermCount {N : Nat} [NeZero N] (A : Finset (ZMod N)) : Nat :=
  countWhere fun p : ZMod N × ZMod N => ∀ i : Fin 4, p.2 - (i : Nat) * p.1 ∈ A

theorem fourTermCount_eq_progressionAverage {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) :
    (fourTermCount A : Complex) = progressionAverage (fun _ : Fin 4 => indicator A) := by
  exact progressionCount_eq_progressionAverage (k := 4) A

theorem fourTermCount_le_modulus_of_no_ap {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (hno : ¬ HasModAP A 4) : fourTermCount A ≤ N := by
  exact progressionCount_le_modulus_of_no_ap A hno

/-- A real lower bound for the actual integer count. -/
theorem relative_fourTermCount_lower {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha 2) :
    delta ^ 4 * fourTermCount S - 4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 ≤
      (fourTermCount A : Real) := by
  have h := relative_fourFactor_counting_bound hN A S delta alpha hAS hδ hδone hα hu
  rw [← fourTermCount_eq_progressionAverage, ← fourTermCount_eq_progressionAverage] at h
  have hr : |(fourTermCount A : Real) - delta ^ 4 * fourTermCount S| ≤
      4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 := by
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using h
  linarith [(abs_le.mp hr).1]

/-- A support count exceeding the error plus all possible constant
progressions forces a nonconstant progression in the original set. -/
theorem relative_uniform_hasModAP_four {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha 2)
    (hcount : (N : Real) + 4 * alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 <
      delta ^ 4 * fourTermCount S) : HasModAP A 4 := by
  by_contra hno
  have hsmall : (fourTermCount A : Real) ≤ N := by
    exact_mod_cast fourTermCount_le_modulus_of_no_ap A hno
  have hlarge := relative_fourTermCount_lower hN A S delta alpha hAS hδ hδone hα hu
  linarith

end LeanProofs.GowersSzemeredi
