import GowersSzemeredi.Proofs18WidthPowerBounds
import GowersSzemeredi.Proofs16FamilyLemma6

/-! The scale conditions of the length-six route.

`length_six_quartic_inverse` needs, at every large prime modulus `N`, the
conditions `SinglePieceModulusConditions`. `ls_modulus_conditions` proves
them above an explicit threshold `lsTloc`, with an explicit exponent `lsE`.

The first step is the nested lift width
`nestW = W(C(C t₂))(W(C t₂)(W t₂ N))`. By `sixW_powerLB` and
`WidthPowerLB.comp` it is at least `N^(a₁a₂a₃)` above an explicit threshold
(`lsNestExp`, `lsNestThr`; `lsNest_powerLB`).

The parameters of the route, `lsNest_powerLB`, `ls_modulus_conditions` and
`length_six_function_discrepancy` are in `Proofs18LengthSixScaleSide`
(`sixW_powerLB` in `Proofs18WidthPowerBoundsSide`), outside the final route.
This module keeps the widths and exponents that the final route uses.

`lsNestExp`, `lsNestExp_le_one`, `lsNestExp_pos`, `lsNestThr` and
`nestW_three_eq` are in `Proofs18LengthSixScaleSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

section Nest

variable (Eb : Nat → Real → Real → Real → Real) (C : Real → Real) (alpha t : Real)

end Nest

/-- `L ↦ coverWidth E t ⌈L/8⌉` is at least `L^(E/2)` above `64`. -/
theorem coverWidth_div8_powerLB (E : Real → Real) (t : Real)
    (hE : 0 < E (t / 2)) :
    WidthPowerLB (fun L => coverWidth E t ⌈(L : Real) / 8⌉₊) (E (t / 2) / 2) 64 := by
  intro L hL
  have hLpos : (0 : Real) < L := by linarith
  have hc := coverWidth_powerLB E t hE.le ⌈(L : Real) / 8⌉₊ (Nat.cast_nonneg _)
  have h8 : (L : Real) / 8 ≤ ⌈(L : Real) / 8⌉₊ := Nat.le_ceil _
  have hp : ((L : Real) / 8) ^ E (t / 2) ≤ (⌈(L : Real) / 8⌉₊ : Real) ^ E (t / 2) :=
    Real.rpow_le_rpow (by positivity) h8 hE.le
  refine le_trans ?_ (hp.trans hc)
  -- `L^(E/2) ≤ (L/8)^E` because `8 ≤ √L`
  have hsq : (8 : Real) ≤ (L : Real) ^ ((1 : Real) / 2) := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : Real) ≤ 64) hL (by norm_num : (0 : Real) ≤ 1 / 2)
    have h64 : (64 : Real) ^ ((1 : Real) / 2) = 8 := by
      rw [show (64 : Real) = 8 ^ (2 : Real) by norm_num, ← Real.rpow_mul (by norm_num)]
      norm_num
    rw [h64] at h
    exact h
  have hsplit : (L : Real) ^ E (t / 2) = (L : Real) ^ (E (t / 2) / 2) *
      ((L : Real) ^ ((1 : Real) / 2)) ^ E (t / 2) := by
    rw [← Real.rpow_mul hLpos.le, ← Real.rpow_add hLpos]
    congr 1
    ring
  rw [Real.div_rpow hLpos.le (by norm_num), hsplit, le_div_iff₀ (by positivity)]
  have h8E : (8 : Real) ^ E (t / 2) ≤ ((L : Real) ^ ((1 : Real) / 2)) ^ E (t / 2) :=
    Real.rpow_le_rpow (by norm_num) hsq hE.le
  have hLE : 0 ≤ (L : Real) ^ (E (t / 2) / 2) := Real.rpow_nonneg hLpos.le _
  nlinarith

/-- The spectrum cell width is monotone in the exponent, for `m ≥ 1`. -/
theorem spectrumCellWidth_mono_exp {zeta : Real} (hz : 0 ≤ zeta) {m : Nat} (hm : 1 ≤ m)
    {e e' : Real} (hee' : e ≤ e') : spectrumCellWidth zeta m e ≤ spectrumCellWidth zeta m e' := by
  unfold spectrumCellWidth
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.sqrt_le_sqrt (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) hee')

/-- The spectrum cell width as a power. -/
theorem spectrumCellWidth_eq {zeta : Real} {m : Nat} {e : Real} :
    spectrumCellWidth zeta m e = zeta / 2 * (m : Real) ^ (e / 2) := by
  unfold spectrumCellWidth
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  ring_nf

/-- The reciprocal-radius and reciprocal-density scales give the two spectrum
cell size conditions of the inverse step. -/
theorem spectrumCellWidth_scale_bounds {zeta rho b e : Real} (hz : 0 < zeta) (hr : 0 < rho)
    {m : Nat} (hm : 1 ≤ m) (he : 2 * b ≤ e)
    (h8 : 8 / zeta ≤ (m : Real) ^ b) (hrho : 4 / (zeta * rho ^ 3) ≤ (m : Real) ^ b) :
    4 ≤ spectrumCellWidth zeta m e ∧ 2 ≤ rho ^ 3 * spectrumCellWidth zeta m e := by
  have hw := spectrumCellWidth_mono_exp hz.le hm he
  rw [spectrumCellWidth_eq, show 2 * b / 2 = b by ring] at hw
  constructor
  · calc 4 = zeta / 2 * (8 / zeta) := by field_simp; ring
         _ ≤ zeta / 2 * (m : Real) ^ b := mul_le_mul_of_nonneg_left h8 (by positivity)
         _ ≤ _ := hw
  · have hr3 : 0 < rho ^ 3 := by positivity
    have h : 2 / rho ^ 3 ≤ spectrumCellWidth zeta m e := by
      calc 2 / rho ^ 3 = zeta / 2 * (4 / (zeta * rho ^ 3)) := by field_simp; ring
           _ ≤ zeta / 2 * (m : Real) ^ b := mul_le_mul_of_nonneg_left hrho (by positivity)
           _ ≤ _ := hw
    simpa only [mul_comm] using (div_le_iff₀ hr3).mp h

/-- Above the reciprocal-radius scale, one eighth of the spectrum cell width
still dominates the half-power of the input length. -/
theorem spectrumCellWidth_div8_ge_rpow {zeta b e : Real} (hz : 0 < zeta)
    {m : Nat} (hm : 1 ≤ m) (he : 2 * b ≤ e)
    (hscale : 16 / zeta ≤ (m : Real) ^ (b / 2)) :
    (m : Real) ^ (b / 2) ≤ spectrumCellWidth zeta m e / 8 := by
  have hmpos : (0 : Real) < m := lt_of_lt_of_le zero_lt_one (by exact_mod_cast hm)
  have hm0 : 0 ≤ (m : Real) ^ (b / 2) := Real.rpow_nonneg hmpos.le _
  have hmono := spectrumCellWidth_mono_exp hz.le hm he
  rw [spectrumCellWidth_eq] at hmono
  have hpow : (m : Real) ^ (2 * b / 2) =
      (m : Real) ^ (b / 2) * (m : Real) ^ (b / 2) := by
    rw [← Real.rpow_add hmpos]; ring_nf
  rw [hpow] at hmono
  have hk : 16 ≤ zeta * (m : Real) ^ (b / 2) := by
    have := mul_le_mul_of_nonneg_left hscale hz.le
    have h16 : zeta * (16 / zeta) = 16 := by field_simp
    linarith
  have hprod := mul_le_mul_of_nonneg_left hk hm0
  have hxx : (m : Real) ^ (b / 2) * (zeta * (m : Real) ^ (b / 2)) =
      zeta / 2 * ((m : Real) ^ (b / 2) * (m : Real) ^ (b / 2)) * 2 := by ring
  rw [hxx] at hprod
  linarith

/-- Composing five exponents in `(0, 1]` preserves that range through the
width products; the final localization exponent, divided by eight, is at most one half. -/
theorem localization_exponents_pos_le {a em b eth ec : Real}
    (ha : 0 < a ∧ a ≤ 1) (hem : 0 < em ∧ em ≤ 1)
    (hb : 0 < b ∧ b ≤ 1) (heth : 0 < eth ∧ eth ≤ 1) (hec : 0 < ec ∧ ec ≤ 1) :
    let m := a * (em / 2)
    let f := m * (b * (eth * ec) / 2)
    0 < f / 8 ∧ f / 8 ≤ 1 / 2 ∧ 0 < f ∧ f ≤ 1 ∧ 0 < m ∧ m ≤ 1 := by
  have hm0 : 0 < a * (em / 2) := mul_pos ha.1 (div_pos hem.1 two_pos)
  have hm1 : a * (em / 2) ≤ 1 :=
    mul_le_one₀ ha.2 (by linarith [hem.1]) (by linarith [hem.2])
  have hee0 := mul_pos heth.1 hec.1
  have hee1 := mul_le_one₀ heth.2 hec.1.le hec.2
  have hin0 : 0 < b * (eth * ec) / 2 := div_pos (mul_pos hb.1 hee0) two_pos
  have hin1 : b * (eth * ec) / 2 ≤ 1 := by
    have := mul_le_one₀ hb.2 hee0.le hee1
    linarith
  have hf0 := mul_pos hm0 hin0
  have hf1 := mul_le_one₀ hm1 hin0.le hin1
  dsimp only
  exact ⟨div_pos hf0 (by norm_num), by linarith, hf0, hf1, hm0, hm1⟩

/-! ### The parameters of the length-six route -/

section Params

variable (A Bq : Nat → Real) (K2 p2 : Nat) (alpha : Real)

def lsT2 : Real := globalTheta2 alpha (alpha / 2) 2
def lsDelta : Real := section16Delta (section16ThetaOne alpha (alpha / 2) 2)
def lsBudget : Real := globalBudget alpha (alpha / 2) 2
def lsZeta : Real := section16Zeta alpha (alpha / 2) 2
end Params

theorem le_rpow_of_rpow_inv_le {T x a : Real} (ha : 0 < a) (hT : 0 ≤ T)
    (h : T ^ (1 / a) ≤ x) : T ≤ x ^ a := by
  have h1 := Real.rpow_le_rpow (Real.rpow_nonneg hT _) h ha.le
  rwa [← Real.rpow_mul hT, show 1 / a * a = 1 by field_simp, Real.rpow_one] at h1

theorem familyRecExp_le_one (k p q : Nat) (hp : 0 < p) : familyRecExp k p q ≤ 1 := by
  unfold familyRecExp
  apply inv_le_one_of_one_le₀
  have : 1 ≤ 2 * (p * (q + 1) ^ (2 * 2 ^ (k + 1))) := by
    have h1 : 1 ≤ (q + 1) ^ (2 * 2 ^ (k + 1)) := Nat.one_le_pow _ _ (by omega)
    have h2 : 1 ≤ p * (q + 1) ^ (2 * 2 ^ (k + 1)) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    omega
  exact_mod_cast this

end LeanProofs.GowersSzemeredi
