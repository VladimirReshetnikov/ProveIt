import GowersSzemeredi.Proofs16DeepBoundSlices
import GowersSzemeredi.Proofs16VarietyLocalPieces

/-! Theorem 16.2 and Corollary 16.11 in dimension three from the eventual,
polynomial-bound deep structure.

The corpus pipeline proves the deep structure in the form
`MilicevicDeepEventuallyPrime Bnd`, with a polynomial bound `Bnd`
(research notes, J.5b caveat). This module derives the dimension-three
statements from it, with the Milićević index chosen per density:
* `exists_milicevicBound_between`: some `D` has
  `B ≤ milicevicBound D c ≤ (4/c)·max B 1`, the least `D` with the first
  inequality;
* `milicevic_choice_le_pow`: if `Bnd c ≤ (4/c)^K` and `4/c ≤ x^k`, that
  index has `milicevicBound D c ≤ x^(k(K+1))`;
* `section16_budgeted_piece_three_of_eventually`: the family index at the
  variety density and the spectrum index at the spectrum density give
  both covers (`variety_structure_class_cover_of_eventually_at`) and
  both Milićević values within budget, for `K ≤ 2^64`;
* `theorem_16_2_at_three_of_eventually_of_constants` and the corollary.
  The named constants enter only through their numeric bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The Milićević base is at most `4/c`. -/
theorem milicevic_base_le_four_div {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) :
    2 + 2 * Real.log c⁻¹ ≤ 4 / c := by
  have hlog : Real.log c⁻¹ ≤ c⁻¹ :=
    (Real.log_le_sub_one_of_pos (inv_pos.mpr hc)).trans (by linarith)
  have hci : 1 ≤ c⁻¹ := (one_le_inv₀ hc).mpr hc1
  rw [div_eq_mul_inv]
  linarith

/-- **A least Milićević index overshoots by at most one base factor.** -/
theorem exists_milicevicBound_between {c : Real} (hc : 0 < c) (hc1 : c ≤ 1) (B : Real) :
    ∃ D : Nat, B ≤ milicevicBound D c ∧ milicevicBound D c ≤ 4 / c * max B 1 := by
  classical
  have hex : ∃ D : Nat, B ≤ milicevicBound D c := exists_milicevicBound_ge hc hc1 B
  have hbase := two_le_milicevic_base hc hc1
  have hb4 := milicevic_base_le_four_div hc hc1
  have hmax : 1 ≤ max B 1 := le_max_right _ _
  have h4c : 4 ≤ 4 / c := by rw [le_div_iff₀ hc]; linarith
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases hD : Nat.find hex with _ | k
  · simp only [milicevicBound, pow_zero]
    nlinarith
  · have hk : ¬ (B ≤ milicevicBound k c) := Nat.find_min hex (by omega)
    push_neg at hk
    unfold milicevicBound at hk ⊢
    rw [pow_succ]
    have hk0 : 0 ≤ (2 + 2 * Real.log c⁻¹) ^ k := pow_nonneg (by linarith) k
    calc (2 + 2 * Real.log c⁻¹) ^ k * (2 + 2 * Real.log c⁻¹)
        ≤ max B 1 * (4 / c) :=
          mul_le_mul (hk.le.trans (le_max_left _ _)) hb4 (by linarith) (by linarith)
      _ = 4 / c * max B 1 := mul_comm _ _

/-- **Under a polynomial bound, the least index stays a power of `x`.** -/
theorem milicevic_choice_le_pow {Bnd : Real → Real} {K : Nat}
    (hBnd : ∀ c : Real, 0 < c → c ≤ 1 → Bnd c ≤ (4 / c) ^ K) {c x : Real} {k : Nat}
    (hc : 0 < c) (hc1 : c ≤ 1) (h4 : 4 / c ≤ x ^ k) :
    ∃ D : Nat, Bnd c ≤ milicevicBound D c ∧ milicevicBound D c ≤ x ^ (k * (K + 1)) := by
  obtain ⟨D, h1, h2⟩ := exists_milicevicBound_between hc hc1 (Bnd c)
  refine ⟨D, h1, h2.trans ?_⟩
  have h41 : 1 ≤ 4 / c := by rw [le_div_iff₀ hc]; linarith
  have hmax : max (Bnd c) 1 ≤ (4 / c) ^ K := max_le (hBnd c hc hc1) (one_le_pow₀ h41)
  calc 4 / c * max (Bnd c) 1 ≤ 4 / c * (4 / c) ^ K :=
        mul_le_mul_of_nonneg_left hmax (by positivity)
    _ = (4 / c) ^ (K + 1) := by ring
    _ ≤ (x ^ k) ^ (K + 1) := pow_le_pow_left₀ (by positivity) h4 _
    _ = x ^ (k * (K + 1)) := by rw [← pow_mul]

/-- **The source's piece budget in dimension three from the eventual,
polynomial-bound deep structure.** -/
theorem section16_budgeted_piece_three_of_eventually {Bnd : Real → Real} {K : Nat}
    (hK : K ≤ 2 ^ 64) (hBnd : ∀ c : Real, 0 < c → c ≤ 1 → Bnd c ≤ (4 / c) ^ K)
    (hM : MilicevicDeepEventuallyPrime Bnd)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700) :
    Section16BudgetedPieceAt 3 := by
  apply section16_budgeted_piece_three_of_local hconst
  intro gamma theta hg hg1 ht ht1
  -- arithmetic facts first: no `linarith` once a big-power hypothesis is in scope
  have ht4 : 0 < theta / 4 := by positivity
  have ht41 : theta / 4 ≤ 1 := by linarith
  have ht2 : 0 < theta / 2 := by positivity
  have ht21 : theta / 2 ≤ 1 := by linarith
  obtain ⟨hc1, hc11⟩ := section16VarietyExtractionDensity_pos_le_one gamma ht4 ht41
  obtain ⟨hc2, hc21⟩ := section16VarietySpectrumDensity_pos_le_one ht2 ht21 hg hg1
  obtain ⟨-, -, hd, hd1⟩ := section16_theta_delta_bounds 2 ht2 ht21 hg hg1
  obtain ⟨hθ1, hθ11⟩ : 0 < section16ThetaOne (theta / 2) gamma 2 / 8 ∧
      section16ThetaOne (theta / 2) gamma 2 / 8 ≤ 1 := by
    obtain ⟨ha, ha1, -, -⟩ := section16_theta_delta_bounds 2 ht2 ht21 hg hg1
    exact ⟨div_pos ha (by norm_num), by linarith⟩
  have hx1 : (1 : Real) ≤ 2 / (theta * gamma) := le_trans (by norm_num) (two_le_two_div ht ht1 hg hg1)
  have hK1 : 2 ^ 27 * (K + 1) ≤ 2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) :=
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hK 1)).trans (by norm_num)
  have hK2 : 2 ^ 158 * (K + 1) ≤ 2 * (2 : Nat) ^ ((2 : Nat) ^ (2 + 6)) :=
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hK 1)).trans (by norm_num)
  -- the two indices
  obtain ⟨D, hD1, hD2⟩ := milicevic_choice_le_pow hBnd hc1 hc11 (variety_density_inv_le ht ht1 hg hg1)
  obtain ⟨D₂, hE1, hE2⟩ := milicevic_choice_le_pow hBnd hc2 hc21
    (spectrum_density_inv_le ht ht1 hg hg1)
  exact ⟨D, D₂, variety_structure_class_cover_of_eventually_at hM gamma (theta / 4) hg hg1 ht4 ht41 hD1,
    variety_structure_class_cover_of_eventually_at hM _ _ hd hd1 hθ1 hθ11 hE1,
    hD2.trans (pow_le_pow_right₀ hx1 hK1), hE2.trans (pow_le_pow_right₀ hx1 hK2)⟩

/-- **Theorem 16.2 in dimension three, from the eventual, polynomial-bound deep structure.** -/
theorem theorem_16_2_at_three_of_eventually_of_constants {Bnd : Real → Real} {K : Nat}
    (hK : K ≤ 2 ^ 64) (hBnd : ∀ c : Real, 0 < c → c ≤ 1 → Bnd c ≤ (4 / c) ^ K)
    (hM : MilicevicDeepEventuallyPrime Bnd)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700) :
    Theorem162At 3 :=
  theorem_16_2_of_budgeted_piece (section16_budgeted_piece_three_of_eventually hK hBnd hM hconst)

/-- **Corollary 16.11 in dimension three, from the eventual, polynomial-bound deep structure.** -/
theorem corollary_16_11_at_three_of_eventually_of_constants {Bnd : Real → Real} {K : Nat}
    (hK : K ≤ 2 ^ 64) (hBnd : ∀ c : Real, 0 < c → c ≤ 1 → Bnd c ≤ (4 / c) ^ K)
    (hM : MilicevicDeepEventuallyPrime Bnd)
    (hconst : (explicitLiftK : Real) ≤ 2 ^ 1700 ∧ (explicitLiftP : Real) ≤ 2 ^ 1700 ∧
      (explicitVarietyK : Real) ≤ 2 ^ 1700 ∧ (explicitVarietyP : Real) ≤ 2 ^ 1700) :
    Corollary1611At 3 :=
  Theorem162At.corollary_16_11 (by norm_num)
    (theorem_16_2_at_three_of_eventually_of_constants hK hBnd hM hconst)

end LeanProofs.GowersSzemeredi
