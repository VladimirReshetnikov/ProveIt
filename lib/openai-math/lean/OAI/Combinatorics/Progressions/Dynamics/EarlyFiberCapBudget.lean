/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Probability.CanonicalConstantDensityBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def earlyFiberCapLog (P : ℝ) : ℝ := 3 * P ^ 3 + 17 * P ^ 2

theorem earlyFiberCapLog_nonneg {P : ℝ} (hP : 0 ≤ P) : 0 ≤ earlyFiberCapLog P := by
  unfold earlyFiberCapLog
  positivity

theorem earlyConstantDensityCap_exp_bound (a n : ℕ) {R V P : ℝ}
    (hP : 0 ≤ P) (hR : 0 < R)
    (ha : (a : ℝ) ≤ P) (hn : (n : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : R⁻¹ ≤ Real.exp P) (hVP : V ≤ Real.exp P) :
    earlyConstantDensityCap a n R V ≤ Real.exp (3 * P ^ 2 + 17 * P) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hw : (R / 4)⁻¹ ≤ Real.exp (P + 4) := by
    calc
      _ = 4 * R⁻¹ := by rw [inv_div, div_eq_mul_inv]
      _ ≤ Real.exp 4 * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, add_comm]
  have hz : 8 * (probabilityProfileLipschitz : ℝ) / (R / 4) ≤ Real.exp (2 * P + 12) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 8 * Real.exp P * Real.exp (P+4) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hwp := pow_le_exp_mul_of_le_exp (by positivity) hw (by positivity) a ha
  have hzp := pow_le_exp_mul_of_le_exp (by positivity) hz (by positivity) n hn
  unfold earlyConstantDensityCap
  calc
    _ ≤ Real.exp P * Real.exp (P * (P+4)) * Real.exp (P * (2*P+12)) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem earlyFiberCap_exp_bound {m : ℕ} (a n : Fin m → ℕ) (R V : Fin m → ℝ) {P : ℝ}
    (hP : 0 ≤ P) (hm : (m : ℝ) ≤ P) (hR : ∀ j, 0 < R j) (hV : ∀ j, 0 ≤ V j)
    (ha : ∀ j, (a j : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hA : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hVP : ∀ j, V j ≤ Real.exp P) :
    (∏ j, earlyConstantDensityCap (a j) (n j) (R j) (V j)) ≤ Real.exp (earlyFiberCapLog P) := by
  calc
    _ ≤ ∏ _j : Fin m, Real.exp (3*P^2+17*P) :=
      Finset.prod_le_prod₀ (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (hV j))
        (fun j _ => earlyConstantDensityCap_exp_bound _ _ hP (hR j)
          (ha j) (hn j) hA (hRP j) (hVP j))
    _ = (Real.exp (3*P^2+17*P))^m := by simp
    _ ≤ Real.exp (P*(3*P^2+17*P)) :=
      pow_le_exp_mul_of_le_exp (Real.exp_nonneg _) le_rfl (by positivity) m hm
    _ = _ := by congr 1; unfold earlyFiberCapLog; ring

end Erdos3

end

end OAI
