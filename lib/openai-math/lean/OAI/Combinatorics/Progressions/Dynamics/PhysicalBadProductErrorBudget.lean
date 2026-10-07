import OAI.Combinatorics.Progressions.Lattices.StrideSelectedResidueBadProduct

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_residue_error_le_of_common_gap {ι : Type*} [Fintype ι]
    (width : ι → ℝ) {A cap W κ : ℝ} (hA : 0 < A) (hcap : 0 ≤ cap)
    (hW : 0 < W) (hwidth : ∀ i, 8 * A * W ≤ width i)
    (hbudget : 2 * (Fintype.card ι : ℝ) * cap ≤ κ * W) :
    (∑ i, 16 * A * cap / width i) ≤ κ := by
  have hterm (i : ι) : 16 * A * cap / width i ≤ 2 * cap / W := by
    calc
      _ ≤ 16 * A * cap / (8 * A * W) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (hwidth i)
      _ = 2 * cap / W := by field_simp; ring
  calc
    _ ≤ ∑ _i : ι, 2 * cap / W := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (2 * (Fintype.card ι : ℝ) * cap) / W := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ ≤ κ := (div_le_iff₀ hW).mpr hbudget

theorem finite_residue_error_common_gap_budget {ι : Type*} [Fintype ι]
    (width : ι → ℝ) {A cap W κ : ℝ} (hA : 0 < A) (hcap : 0 < cap)
    (hκ : 0 < κ) (hcapW : cap ≤ W) (hwidth : ∀ i, 8 * A * W ≤ width i)
    (hWbudget : 2 * (Fintype.card ι : ℝ) * cap / κ ≤ W) :
    (∀ i, 8 * A * cap ≤ width i) ∧ (∑ i, 16 * A * cap / width i) ≤ κ := by
  refine ⟨fun i => (mul_le_mul_of_nonneg_left hcapW (by positivity)).trans (hwidth i), ?_⟩
  apply finite_residue_error_le_of_common_gap width hA hcap.le (hcap.trans_le hcapW) hwidth
  have h := (div_le_iff₀ hκ).mp hWbudget
  simpa only [mul_comm] using h

noncomputable def physicalBadProductAccuracy (E Vlog : ℝ) : ℝ :=
  Real.exp (-(Vlog + 3 * E + 16))

theorem physicalBadProductAccuracy_pos (E Vlog : ℝ) :
    0 < physicalBadProductAccuracy E Vlog := Real.exp_pos _

theorem physicalBadProductAccuracy_inv (E Vlog : ℝ) :
    (physicalBadProductAccuracy E Vlog)⁻¹ = Real.exp (Vlog + 3 * E + 16) := by
  unfold physicalBadProductAccuracy
  rw [Real.exp_neg, inv_inv]

private theorem exp_eight_ge : (128 : ℝ) ≤ Real.exp 8 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h1 8
  have he : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
    simp
  rw [he]
  norm_num at hpow ⊢
  linarith

theorem physicalBadProductAccuracy_budget {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    let κ := physicalBadProductAccuracy E Vlog
    let R := quantitativeBadPrimeRadius E
    let η := Real.exp (-E) / (2 * ((Q : ℝ) + (R : ℝ) ^ 2))
    0 < κ ∧ κ⁻¹ = Real.exp (Vlog + 3 * E + 16) ∧
      2 * κ + κ ≤ 1 / 2 ∧ 128 * κ ≤ η ∧
      12 * (2 * κ + κ) + κ ≤ η := by
  dsimp only
  let T := Vlog + 3 * E + 8
  let η := Real.exp (-E) / (2 * ((Q : ℝ) + (quantitativeBadPrimeRadius E : ℝ) ^ 2))
  have hη : 0 < η := (quantitativeBadPrimeRadius_error hE Q hQ).1
  have hi : 1 / η ≤ Real.exp T :=
    (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).2
  have hlo : Real.exp (-T) ≤ η := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos T)).mpr
    have hh := (div_le_iff₀ hη).mp hi
    simpa only [mul_comm] using hh
  have heq : physicalBadProductAccuracy E Vlog = Real.exp (-T) / Real.exp 8 := by
    rw [physicalBadProductAccuracy, ← Real.exp_sub]
    congr 1
    dsimp [T]
    ring
  have h128 : 128 * physicalBadProductAccuracy E Vlog ≤ η := by
    rw [heq]
    apply le_trans _ hlo
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (Real.exp_pos 8)).mpr
    have h := mul_le_mul_of_nonneg_left exp_eight_ge (Real.exp_pos (-T)).le
    nlinarith
  have hκ := physicalBadProductAccuracy_pos E Vlog
  have hκsmall : physicalBadProductAccuracy E Vlog ≤ 1 / 128 := by
    have hT : 0 ≤ T := by dsimp [T]; linarith
    have hl : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT)
    have hh : physicalBadProductAccuracy E Vlog * Real.exp 8 = Real.exp (-T) := by
      rw [heq, div_mul_cancel₀ _ (Real.exp_pos 8).ne']
    have h := mul_le_mul_of_nonneg_left exp_eight_ge hκ.le
    nlinarith
  refine ⟨hκ, physicalBadProductAccuracy_inv E Vlog, ?_, h128, ?_⟩
  · linarith
  · linarith

noncomputable def physicalBadProductGap (N : ℕ) (E Vlog : ℝ) (Q : ℕ) : ℝ :=
  (2 * (N : ℝ) + 1) * (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) /
    physicalBadProductAccuracy E Vlog

theorem physicalBadProductGap_budget (N : ℕ) {E Vlog : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (Q : ℕ) (hQ : 1 ≤ Q)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) :
    1 ≤ physicalBadProductGap N E Vlog Q ∧
    (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) ≤ physicalBadProductGap N E Vlog Q ∧
    2 * (N : ℝ) * (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) /
      physicalBadProductAccuracy E Vlog ≤ physicalBadProductGap N E Vlog Q := by
  have hb := physicalBadProductAccuracy_budget hE hVlog Q hQ hQexp
  have hκ := hb.1
  have hκ1 : physicalBadProductAccuracy E Vlog ≤ 1 := by linarith [hb.2.2.1]
  have hc : (1 : ℝ) ≤ (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) := by
    exact_mod_cast hQ.trans (le_max_left _ _)
  have hW : (max Q ((quantitativeBadPrimeRadius E) ^ 2) : ℕ) ≤ physicalBadProductGap N E Vlog Q := by
    unfold physicalBadProductGap
    apply (le_div_iff₀ hκ).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  refine ⟨hc.trans hW, hW, ?_⟩
  unfold physicalBadProductGap
  exact div_le_div_of_nonneg_right (by nlinarith) hκ.le

theorem physicalBadProductGap_exp_bound (N : ℕ) {E Vlog F : ℝ}
    (hE : 0 ≤ E) (hVlog : 0 ≤ Vlog) (hF : 0 ≤ F) (Q : ℕ)
    (hQexp : (Q : ℝ) ≤ Real.exp Vlog) (hN : (N : ℝ) ≤ Real.exp F) :
    physicalBadProductGap N E Vlog Q ≤ Real.exp (F + 2 * Vlog + 5 * E + 24) := by
  have hcap := (quantitativeBadPrimeRadius_witness_budget hE hVlog Q hQexp).1
  have he2 : (3 : ℝ) ≤ Real.exp 2 := by
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hh := mul_le_mul he1 he1 (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos 1).le
    have hid : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [hid]
    nlinarith
  have hn : 2 * (N : ℝ) + 1 ≤ Real.exp (F + 2) := by
    rw [Real.exp_add]
    have hf := Real.one_le_exp hF
    have hh := mul_le_mul_of_nonneg_left he2 (Real.exp_pos F).le
    nlinarith
  unfold physicalBadProductGap
  rw [div_eq_mul_inv, physicalBadProductAccuracy_inv]
  calc
    _ ≤ Real.exp (F + 2) * Real.exp (Vlog + 2 * E + 6) * Real.exp (Vlog + 3 * E + 16) := by
      gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
