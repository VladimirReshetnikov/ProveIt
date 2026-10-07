import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem real_fourierChar_norm_sub_le (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      2 * Real.pi * |a - b| := by
  have hmul : (Real.fourierChar a : ℂ) =
      (Real.fourierChar (a - b) : ℂ) * (Real.fourierChar b : ℂ) := by
    rw [← Circle.coe_mul, ← Real.fourierChar.map_add_eq_mul, sub_add_cancel]
  calc
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ =
        ‖((Real.fourierChar (a - b) : ℂ) - 1) * (Real.fourierChar b : ℂ)‖ := by
      rw [sub_mul, one_mul, ← hmul]
    _ = ‖(Real.fourierChar (a - b) : ℂ) - 1‖ := by
      rw [norm_mul, Circle.norm_coe, mul_one]
    _ ≤ ‖2 * Real.pi * (a - b)‖ := by
      rw [Real.fourierChar_apply, mul_comm _ Complex.I]
      exact Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * |a - b| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]

theorem real_fourierChar_norm_sub_le_four_mul (a b : ℝ) :
    ‖(Real.fourierChar a : ℂ) - (Real.fourierChar b : ℂ)‖ ≤
      4 * Real.pi * |a - b| := by
  refine (real_fourierChar_norm_sub_le a b).trans ?_
  exact mul_le_mul_of_nonneg_right (by nlinarith [Real.pi_pos]) (abs_nonneg _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

variable {m : ℕ}

noncomputable def rationalLiftCharacterTwist (M : ℕ) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (y : Fin m → ℝ) (r : Fin m → ZMod M) : ℂ :=
  Real.fourierChar ((∑ i, (a i : ℝ) * (y i + (r i).val + c i)) / (M : ℝ))

noncomputable def rationalLiftCharacterTwistLip (M : ℕ) (a : Fin m → ℤ) : ℝ≥0 :=
  ⟨2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ), by positivity⟩

theorem rationalLiftCharacterTwist_norm (M : ℕ) (a : Fin m → ℤ) (c y : Fin m → ℝ)
    (r : Fin m → ZMod M) : ‖rationalLiftCharacterTwist M a c y r‖ = 1 :=
  Circle.norm_coe _

theorem rationalLiftCharacterTwist_lipschitz (M : ℕ) (a : Fin m → ℤ) (c : Fin m → ℝ)
    (r : Fin m → ZMod M) :
    LipschitzWith (rationalLiftCharacterTwistLip M a) (fun y => rationalLiftCharacterTwist M a c y r) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm]
  have hdiff : |(∑ i, (a i : ℝ) * (x i + (r i).val + c i)) / (M : ℝ) -
      (∑ i, (a i : ℝ) * (y i + (r i).val + c i)) / (M : ℝ)| ≤
      (∑ i, |(a i : ℝ)|) / (M : ℝ) * dist x y := by
    rw [← sub_div, ← Finset.sum_sub_distrib]
    have heq : (∑ i, ((a i : ℝ) * (x i + (r i).val + c i) -
        (a i : ℝ) * (y i + (r i).val + c i))) =
        ∑ i, (a i : ℝ) * (x i - y i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [heq, abs_div, abs_of_nonneg (Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
    calc
      _ ≤ (∑ i, |(a i : ℝ) * (x i - y i)|) / (M : ℝ) :=
        div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (Nat.cast_nonneg M)
      _ ≤ (∑ i, |(a i : ℝ)| * dist x y) / (M : ℝ) := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg M)
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  change ‖(Real.fourierChar _ : ℂ) - (Real.fourierChar _ : ℂ)‖ ≤ _
  apply (real_fourierChar_norm_sub_le _ _).trans
  apply (mul_le_mul_of_nonneg_left hdiff (by positivity : 0 ≤ 2 * Real.pi)).trans_eq
  change 2 * Real.pi * ((∑ i, |(a i : ℝ)|) / (M : ℝ) * dist x y) =
    (2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ)) * dist x y
  ring

theorem rationalLiftCharacterTwistLip_le (M : ℕ) (hM : 0 < M) (a : Fin m → ℤ)
    (A : ℝ) (ha : ∀ i, |(a i : ℝ)| ≤ A) :
    (rationalLiftCharacterTwistLip M a : ℝ) ≤ 2 * Real.pi * m * A := by
  have hs : (∑ i, |(a i : ℝ)|) ≤ (m : ℝ) * A := by
    calc
      _ ≤ ∑ _i : Fin m, A := Finset.sum_le_sum (fun i _ => ha i)
      _ = _ := by simp
  change 2 * Real.pi * (∑ i, |(a i : ℝ)|) / (M : ℝ) ≤ _
  apply (div_le_self (by positivity)
    (show (1 : ℝ) ≤ M by exact_mod_cast Nat.succ_le_of_lt hM)).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ 2 * Real.pi)

theorem rationalLiftCharacterTwist_residual (M : ℕ) (hM : 0 < M)
    (a : Fin m → ℤ) (c x : Fin m → ℝ) (β : Fin m → ℤ) :
    rationalLiftCharacterTwist M a c (fun i => x i - (β i : ℝ))
      (fun i => (β i : ZMod M)) =
        (Real.fourierChar ((∑ i, (a i : ℝ) * (x i + c i)) / (M : ℝ)) : ℂ) := by
  let : NeZero M := ⟨hM.ne'⟩
  have hzexists (i : Fin m) : ∃ z : ℤ,
      β i = ((β i : ZMod M).val : ℤ) + (M : ℤ) * z :=
    (ZMod.intCast_eq_iff M (β i) (β i : ZMod M)).mp rfl
  choose z hz using hzexists
  have hβ (i : Fin m) : (β i : ℝ) = ((β i : ZMod M).val : ℝ) + (M : ℝ) * (z i : ℝ) := by
    exact_mod_cast hz i
  have hMr : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hphase : (∑ i, (a i : ℝ) * (x i - (β i : ℝ) + (β i : ZMod M).val + c i)) / (M : ℝ) =
      (∑ i, (a i : ℝ) * (x i + c i)) / (M : ℝ) - ((∑ i, a i * z i : ℤ) : ℝ) := by
    calc
      _ = ∑ i, ((a i : ℝ) * (x i + c i) / (M : ℝ) - ((a i * z i : ℤ) : ℝ)) := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        rw [hβ i, Int.cast_mul]
        field_simp
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Int.cast_sum]
        simp only [div_eq_mul_inv, Finset.sum_mul]
  have hzchar : Real.fourierChar (((∑ i, a i * z i : ℤ) : ℝ)) = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * (((∑ i, a i * z i : ℤ) : ℝ))) : ℂ) = 1
    rw [mul_comm (2 * Real.pi), Circle.exp_intCast_mul]
    simp
  unfold rationalLiftCharacterTwist
  rw [hphase, Real.fourierChar.map_sub_eq_div, hzchar, div_one]

end Erdos3

end

end OAI
