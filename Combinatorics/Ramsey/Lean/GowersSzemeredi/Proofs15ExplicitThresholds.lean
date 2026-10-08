import GowersSzemeredi.Proofs15ZeroDensityRestriction

/-! Lemma 15.6 (density-lower-bound form) with an explicit modulus threshold.

`lemma_15_6_of_density_lower_all` states its modulus threshold
existentially. The proofs below repeat those arguments with the explicit
selection estimates (`selection_scale_estimate_explicit`,
`selection_scale_estimate_zero_explicit`), so the threshold becomes the
closed expression `lemma156ExplicitThreshold k beta gamma`. Explicit
thresholds are needed wherever a downstream statement fixes its own
numerical threshold, such as Theorem 18.2. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The explicit modulus threshold of Lemma 15.6 for density lower bound
`beta` and product parameter `gamma`. -/
def lemma156ExplicitThreshold (k : Nat) (beta gamma : Real) : Real :=
  if k = 0 then
    selectionExplicitThreshold 0 (beta ^ 28 * gamma ^ 56) ((2 : Real)⁻¹ ^ 44) 1 (2 * 4 ^ 16)
  else
    selectionExplicitThreshold k (beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1)))
      ((2 : Real)⁻¹ ^ 44) 1 ((3 : Real) ^ (16 * 2 ^ k) * k)

theorem selection_eta_lt_one : ((2 : Real)⁻¹ ^ 44) < 1 :=
  pow_lt_one₀ (by norm_num) (by norm_num) (by norm_num)

/-- `lemma_15_6_of_density_lower` with its threshold written out. -/
theorem lemma_15_6_of_density_lower_explicit (k : Nat) (beta gamma : Real)
    (hk : 1 ≤ k) (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N], lemma156ExplicitThreshold k beta gamma ≤ (N : Real) →
      N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        beta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) * (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  let alpha := beta ^ (7 * 4 ^ (k + 1)) * gamma ^ (21 * k * 4 ^ (k + 1))
  let eta := (2 : Real)⁻¹ ^ 44
  have ha : 0 < alpha := mul_pos (pow_pos hb _) (pow_pos hg _)
  have he : 0 < eta := by dsimp [eta]; positivity
  have hk0 : k ≠ 0 := by omega
  intro N _ hN hp ho B phi hB hprod
  have hN' : selectionExplicitThreshold k alpha eta 1 ((3 : Real) ^ (16 * 2 ^ k) * k) ≤
      (N : Real) := by
    simpa only [lemma156ExplicitThreshold, hk0, if_false] using hN
  have hNp : 0 < (N : Real) ^ (k + 1) := pow_pos (by exact_mod_cast NeZero.pos N) _
  let b : Real := (B.card : Real) / (N : Real) ^ (k + 1)
  have hbb : beta ≤ b := (le_div_iff₀ hNp).mpr hB
  have hbpos : 0 < b := hb.trans_le hbb
  have hcard : (B.card : Real) = b * (N : Real) ^ (k + 1) := by
    dsimp [b]
    field_simp
  have hbupper : b ≤ 1 := by
    apply (div_le_one hNp).mpr
    exact_mod_cast (show B.card ≤ N ^ (k + 1) by
      simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hu : (generalArrangementCount 8 B : Real) ≤ 1 * (N : Real) ^ (17 * k + 15) := by
    exact (selection_arrangement_real_upper b B hcard).trans
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbpos.le hbupper) (by positivity))
  have hl : alpha * 1 * (N : Real) ^ (17 * k + 15) ≤
      respectedGeneralArrangementCount 8 B phi := by
    have hc := lemma_14_8_holds N k b gamma B phi hk hbpos hg hg1 hcard hprod
    apply le_trans ?_ hc
    dsimp [alpha]
    simp only [mul_one]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hb.le hbb _)
        (pow_nonneg hg.le _)) (by positivity)
  obtain ⟨B', hsub, hcount, hrespect⟩ :=
    selection_scale_estimate_explicit k alpha 1 eta hk ha (by norm_num) he
      selection_eta_lt_one N hN' hp ho B phi hu hl
  refine ⟨B', hsub, ?_, hrespect⟩
  have hcoef := lemma156_coefficient_without_density_factor k hk hb hb1 hg hg1
  exact (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
    (by simpa [alpha, eta] using hcount)

/-- `lemma_15_6_zero_of_density_lower` with its threshold written out. -/
theorem lemma_15_6_zero_of_density_lower_explicit (beta gamma : Real)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N], lemma156ExplicitThreshold 0 beta gamma ≤ (N : Real) →
      ∀ (B : Finset (Point N 1)) (phi : Point N 1 → ZMod N),
        beta * (N : Real) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N 1), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (0 + 5))) * (N : Real) ^ 15 ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  let alpha := beta ^ 28 * gamma ^ 56
  let eta := (2 : Real)⁻¹ ^ 44
  have ha : 0 < alpha := mul_pos (pow_pos hb _) (pow_pos hg _)
  have he : 0 < eta := by dsimp [eta]; positivity
  intro N _ hN B phi hB hprod
  have hN' : selectionExplicitThreshold 0 alpha eta 1 (2 * 4 ^ 16) ≤ (N : Real) := by
    simpa only [lemma156ExplicitThreshold, if_true] using hN
  have hNp : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let b : Real := (B.card : Real) / N
  have hbb : beta ≤ b := (le_div_iff₀ hNp).mpr hB
  have hbpos : 0 < b := hb.trans_le hbb
  have hcard : (B.card : Real) = b * (N : Real) ^ (0 + 1 : Nat) := by
    simp only [Nat.zero_add, pow_one]
    dsimp [b]
    field_simp
  have hbupper : b ≤ 1 := by
    apply (div_le_one hNp).mpr
    exact_mod_cast (show B.card ≤ N by
      simpa [Point, ZMod.card] using Finset.card_le_univ B)
  have hu : (generalArrangementCount 8 B : Real) ≤ 1 * (N : Real) ^ 15 := by
    exact (selection_arrangement_real_upper b B hcard).trans
      (mul_le_mul_of_nonneg_right (pow_le_one₀ hbpos.le hbupper) (by positivity))
  have hl : alpha * 1 * (N : Real) ^ 15 ≤ respectedGeneralArrangementCount 8 B phi := by
    simpa only [mul_one] using productProperty_zero_eight_arrangements B phi hb hg hB hprod
  obtain ⟨B', hsub, hcount, hrespect⟩ :=
    selection_scale_estimate_zero_explicit alpha 1 eta ha (by norm_num) he
      selection_eta_lt_one N hN' B phi hu hl
  refine ⟨B', hsub, ?_, hrespect⟩
  exact (mul_le_mul_of_nonneg_right (lemma156_zero_coefficient hb hb1 hg hg1)
    (by positivity)).trans (by simpa only [alpha, eta, mul_one] using hcount)

/-- `lemma_15_6_of_density_lower_all` with its threshold written out. -/
theorem lemma_15_6_of_density_lower_all_explicit (k : Nat) (beta gamma : Real)
    (hb : 0 < beta) (hb1 : beta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    ∀ (N : Nat) [NeZero N], lemma156ExplicitThreshold k beta gamma ≤ (N : Real) →
      N.Prime → Odd N →
      ∀ (B : Finset (Point N (k + 1))) (phi : Point N (k + 1) → ZMod N),
        beta * (N : Real) ^ (k + 1) ≤ B.card → HasProductProperty B phi gamma →
        ∃ B' : Finset (Point N (k + 1)), B' ⊆ B ∧
          (beta * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) * (N : Real) ^ (17 * k + 15) ≤
            generalArrangementCount 8 B' ∧
          (1 - (2 : Real)⁻¹ ^ 44) * generalArrangementCount 8 B' ≤
            respectedGeneralArrangementCount 8 B' phi := by
  by_cases hk : k = 0
  · subst k
    intro N _ hN _ _ B phi hB hprod
    exact lemma_15_6_zero_of_density_lower_explicit beta gamma hb hb1 hg hg1 N hN B phi
      (by simpa using hB) hprod
  · exact lemma_15_6_of_density_lower_explicit k beta gamma (by omega) hb hb1 hg hg1

/-- The explicit form implies the existential one, with the ceiling of the
explicit threshold as witness. -/
theorem lemma156ExplicitThreshold_witness (k : Nat) (beta gamma : Real) (N : Nat)
    (hN : ⌈lemma156ExplicitThreshold k beta gamma⌉₊ ≤ N) :
    lemma156ExplicitThreshold k beta gamma ≤ (N : Real) :=
  (Nat.le_ceil _).trans (by exact_mod_cast hN)

end LeanProofs.GowersSzemeredi
