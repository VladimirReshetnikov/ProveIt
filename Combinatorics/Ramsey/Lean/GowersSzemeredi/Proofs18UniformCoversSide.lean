import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs16SplitAllDimensionsSide
import GowersSzemeredi.Proofs18LengthSixExponentsSide

/-! Declarations of `Proofs18UniformCovers` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-! ### Dimension one -/

/-- **Dimension one with the uniform control**, at any `D ≥ 2^132`. -/
theorem polyCoverAt_one_uniform {V : Real} (hV : 1 ≤ V) {D : Nat} (hD : 2 ^ 132 ≤ D) :
    PolyCoverAt 1 (uCount V D) (uExp V D) := by
  have hw2 : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 → (2 : Real) ≤ 2 / (gamma * theta * rho) := by
    intro gamma theta rho hg hg1 ht ht1 hr hr1
    obtain ⟨hv2, hvw, -⟩ := prod_scale_radius_bounds hg hg1 ht ht1 hr hr1
    exact hv2.trans hvw
  refine polyCoverAt_one.weaken ?_ ?_ ?_
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    have hw2' := hw2 gamma theta rho hg hg1 ht ht1 hr hr1
    have hw0 : (0 : Real) ≤ 2 / (gamma * theta * rho) := le_trans zero_le_two hw2'
    have hu1 : (1 : Real) ≤ uniformBase V 1 theta gamma rho :=
      le_trans one_le_two (hw2'.trans hw)
    have hmono : (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 90) ≤ uCount V D gamma theta rho := by
      unfold uCount
      exact le_max_of_le_right ((pow_le_pow_left₀ hw0 hw _).trans
        (pow_le_pow_right₀ hu1 ((show (2 : Nat) ^ 90 ≤ 2 ^ 132 by norm_num).trans hD)))
    have h := sixQb_le_power 1 hg hg1 ht ht1 hr hr1
    rw [sixQb, if_pos rfl] at h
    exact h.trans hmono
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    exact (uExp_pos hV D hg hg1 ht ht1 hr hr1).1
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    have hw2' := hw2 gamma theta rho hg hg1 ht ht1 hr hr1
    have hw0 : (0 : Real) ≤ 2 / (gamma * theta * rho) := le_trans zero_le_two hw2'
    have hu1 : (1 : Real) ≤ uniformBase V 1 theta gamma rho :=
      le_trans one_le_two (hw2'.trans hw)
    have hK : ((1 : Nat) : Real) ≤ (2 / (gamma * theta * rho)) ^ 3 := by
      rw [Nat.cast_one]; exact one_le_pow₀ (le_trans one_le_two hw2')
    have hpos : 0 < cubicBaseExponent (section16BaseFamilyBound gamma theta) rho :=
      cubicBaseExponent_pos (section16BaseFamilyBound_pos gamma theta) hr
    have hmono : (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 132) ≤ uCount V D gamma theta rho := by
      unfold uCount
      exact le_max_of_le_right ((pow_le_pow_left₀ hw0 hw _).trans (pow_le_pow_right₀ hu1 hD))
    have h := sixEb_inv_le_power 1 (K1 := 1) (p1 := 1) one_pos one_pos hg hg1 ht ht1 hr hr1 hK hK
    rw [sixEb, if_pos rfl] at h
    have hB := h.trans hmono
    have := inv_anti₀ (inv_pos.mpr hpos) hB
    rw [inv_inv] at this
    exact this

/-- The split degrees fit the uniform degree. -/
theorem split_pair_le_uDeg {l : Nat} (hl : 2 ≤ l) :
    (splitPair l).1 + (splitPair l).2 + l + 1 ≤ uDeg l := by
  obtain ⟨-, -, hA, hD⟩ := split_pair_bounds l hl
  have ha : (splitPair l).1 ≤ 2 ^ (35 * 2 ^ l) :=
    le_trans (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)) hA
  have h3575 : 2 ^ (35 * 2 ^ l) ≤ 2 ^ (75 * 2 ^ l) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hlA : l + 1 ≤ 2 ^ (75 * 2 ^ l) := by
    have h1 : l + 1 ≤ 2 ^ (l + 1) := Nat.lt_two_pow_self.le
    have h2 : l + 1 ≤ 75 * 2 ^ l := by
      have := Nat.lt_two_pow_self (n := l); omega
    exact h1.trans (Nat.pow_le_pow_right (by norm_num) h2)
  unfold uDeg
  have h76 : 2 ^ (76 * 2 ^ l) = 2 ^ (75 * 2 ^ l) * 2 ^ (2 ^ l) := by
    rw [← pow_add]; congr 1; ring
  have h4 : 4 ≤ 2 ^ (2 ^ l) := by
    have : 2 ≤ 2 ^ l := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 ^ l) := Nat.pow_le_pow_right (by norm_num) this
  rw [h76]
  nlinarith [Nat.zero_le (2 ^ (75 * 2 ^ l))]

/-- **Uniform covers in every dimension up to `k`**, from the family lemmas. -/
theorem uniformCovers_of_classes (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (k : Nat) : UniformCovers k (classV Kc pc k) (uDeg k) := by
  intro l hl1 hlk
  have hVk := one_le_classV Kc pc k
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine polyCoverAt_one_uniform hVk ?_
    unfold uDeg
    have : 132 ≤ 76 * 2 ^ k := by
      have : 2 ≤ 2 ^ k := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.pow_le_pow_right (by norm_num) this
  · obtain ⟨C⟩ := splitUniformClass_all Kc pc hK hp hlem l hl
    have hVl := one_le_classV Kc pc l
    have hfit := split_pair_le_uDeg hl
    have P0 := (C.toPower hVl).polyCoverAt (by omega) hVl (D := uDeg l) (by omega) (by omega)
      (by omega)
    have P : PolyCoverAt l (uCount (classV Kc pc l) (uDeg l)) (uExp (classV Kc pc l) (uDeg l)) := by
      refine P0.weaken ?_ ?_ ?_
      · intro g t s hg hg1 ht ht1 hs hs1
        rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
      · intro g t s _ _ _ _ _ _
        exact (uExp_pos_le _ _ g t s).1
      · intro g t s hg hg1 ht ht1 hs hs1
        show (uCount _ _ g t s)⁻¹ ≤ _
        rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    exact P.uniform_mono hVl (classV_mono Kc pc hlk)
      (Nat.pow_le_pow_right (by norm_num)
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlk)))

end

end LeanProofs.GowersSzemeredi
