import GowersSzemeredi.Proofs03AnyFactorBound
import GowersSzemeredi.Proofs18RelativeProgressionCount

/-! Relative progression counting at every length, with the original
uniformity degree k-2 and the sharp telescoping factor k. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def telescopingFactor {k : Nat} (f g : Fin k → Complex) (j i : Fin k) : Complex :=
  if i < j then g i else if i = j then f i - g i else f i

theorem fin_product_telescoping (k : Nat) (f g : Fin k → Complex) :
    (∏ i, f i) - (∏ i, g i) = ∑ j, ∏ i, telescopingFactor f g j i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hz : (∏ i, telescopingFactor f g 0 i) = (f 0 - g 0) * ∏ i : Fin k, f i.succ := by
      simp [Fin.prod_univ_succ, telescopingFactor]
    have hj (j : Fin k) : (∏ i, telescopingFactor f g j.succ i) =
        g 0 * ∏ i, telescopingFactor (fun i => f i.succ) (fun i => g i.succ) j i := by
      simp [Fin.prod_univ_succ, telescopingFactor]
    rw [Fin.sum_univ_succ, hz]
    simp_rw [hj]
    rw [← Finset.mul_sum, ← ih, Fin.prod_univ_succ, Fin.prod_univ_succ]
    ring

def progressionTelescopingFamily {N k : Nat} (f g : ZMod N → Complex) (j : Fin k) :
    Fin k → ZMod N → Complex :=
  fun i => if i < j then g else if i = j then f - g else f

theorem progressionAverage_telescoping {N k : Nat} [NeZero N] (f g : ZMod N → Complex) :
    progressionAverage (fun _ : Fin k => f) - progressionAverage (fun _ : Fin k => g) =
      ∑ j : Fin k, progressionAverage (progressionTelescopingFamily f g j) := by
  unfold progressionAverage
  simp only [← Finset.sum_sub_distrib]
  simp_rw [fin_product_telescoping]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.prod_congr rfl
  intro i _
  simp only [telescopingFactor, progressionTelescopingFamily]
  split_ifs <;> rfl

/-- Replacing one bounded function by another costs at most k generalized
von Neumann errors when the difference is uniform of degree k-2. -/
theorem progressionAverage_counting_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hN : k ≤ N) (f g : ZMod N → Complex)
    (hf : DiscValued f) (hg : DiscValued g) (hh : DiscValued (f - g))
    (alpha : Real) (hα : 0 ≤ alpha) (hu : UniformOfDegree (f - g) alpha (k - 2)) :
    ‖progressionAverage (fun _ : Fin k => f) - progressionAverage (fun _ : Fin k => g)‖ ≤
      k * alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
  have hb (j : Fin k) : ‖progressionAverage (progressionTelescopingFamily f g j)‖ ≤
      alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
    refine progressionAverage_uniform_bound hk hN _ ?_ alpha hα j ?_
    · intro i
      unfold progressionTelescopingFamily
      split_ifs <;> assumption
    · simpa [progressionTelescopingFamily] using hu
  rw [progressionAverage_telescoping]
  calc
    _ ≤ ∑ j : Fin k, ‖progressionAverage (progressionTelescopingFamily f g j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin k, alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 :=
      Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp [mul_assoc]

/-- Compare counts in A and in its support S using relative uniformity. -/
theorem relative_progression_counting_bound {N k : Nat} [NeZero N] [Fact N.Prime]
    (hk : 2 ≤ k) (hN : k ≤ N) (A S : Finset (ZMod N)) (delta alpha : Real)
    (hAS : A ⊆ S) (hδ : 0 ≤ delta) (hδone : delta ≤ 1) (hα : 0 ≤ alpha)
    (hu : UniformOfDegree (relativeBalanced A S delta) alpha (k - 2)) :
    ‖progressionAverage (fun _ : Fin k => indicator A) -
        (delta : Complex) ^ k * progressionAverage (fun _ : Fin k => indicator S)‖ ≤
      k * alpha ^ (1 / (2 : Real) ^ (k - 1)) * (N : Real) ^ 2 := by
  classical
  have hf : DiscValued (indicator A) := by
    intro x
    by_cases hx : x ∈ A <;> simp [indicator, hx]
  have hg : DiscValued (fun x => (delta : Complex) * indicator S x) := by
    intro x
    by_cases hx : x ∈ S
    · simpa [indicator, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ] using hδone
    · simp [indicator, hx]
  have heq : indicator A - (fun x => (delta : Complex) * indicator S x) =
      relativeBalanced A S delta := by
    funext x
    exact (relativeBalanced_eq_indicators A S delta x).symm
  have h := progressionAverage_counting_bound hk hN (indicator A) (fun x => (delta : Complex) * indicator S x)
    hf hg (heq ▸ relativeBalanced_discValued A S delta hAS hδ hδone) alpha hα (heq ▸ hu)
  rwa [progressionAverage_const_mul] at h

end LeanProofs.GowersSzemeredi
