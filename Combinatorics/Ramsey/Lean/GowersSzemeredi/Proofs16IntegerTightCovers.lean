import GowersSzemeredi.Proofs16IntegerSplitClasses
import GowersSzemeredi.Proofs18TightClasses

/-! Polynomial covers with ordinary integer geometry and degree 2^(68*2^k).
The stronger split recurrence avoids the coarse triple-exponential degree
in the earlier integer-cover wrapper. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem IntegerPolyCoverAt.weaken {l : Nat} {Q E Q' E' : Real → Real → Real → Real}
    (h : IntegerPolyCoverAt l Q E)
    (hQ : ∀ g t s, 0 < g → g ≤ 1 → 0 < t → t ≤ 1 → 0 < s → s ≤ 1 → Q g t s ≤ Q' g t s)
    (hE0 : ∀ g t s, 0 < g → g ≤ 1 → 0 < t → t ≤ 1 → 0 < s → s ≤ 1 → 0 < E' g t s)
    (hE : ∀ g t s, 0 < g → g ≤ 1 → 0 < t → t ≤ 1 → 0 < s → s ≤ 1 → E' g t s ≤ E g t s) :
    IntegerPolyCoverAt l Q' E' := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  obtain ⟨J, hJ, hML⟩ := h N gamma theta hg hg1 ht ht1 Gamma hsize hprod
  exact ⟨J, hJ, hML.weaken (fun s hs hs1 => hQ gamma theta s hg hg1 ht ht1 hs hs1)
    (fun s hs hs1 => hE0 gamma theta s hg hg1 ht ht1 hs hs1)
    (fun s hs hs1 => hE gamma theta s hg hg1 ht ht1 hs hs1)⟩

theorem integerPolyCoverAt_one_uniform_low {V : Real} (hV : 1 ≤ V) {D : Nat} (hD : 2 ^ 17 ≤ D) :
    IntegerPolyCoverAt 1 (uCount V D) (uExp V D) := by
  have hbase : ∀ gamma theta rho : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
      0 < rho → rho ≤ 1 →
      (2 : Real) ≤ 2 / (gamma * theta * rho) ∧ rho⁻¹ ≤ (2 / (gamma * theta * rho)) ^ 1 ∧
      (section16BaseFamilyBound gamma theta : Real) ≤
        (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 14) := by
    intro gamma theta rho hg hg1 ht ht1 hr hr1
    have hgt : 0 < gamma * theta := mul_pos hg ht
    have hgt1 : gamma * theta ≤ 1 := mul_le_one₀ hg1 ht.le ht1
    have hvw : 2 / (gamma * theta) ≤ 2 / (gamma * theta * rho) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos hgt hr) (by nlinarith)
    obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
    have hB := section16BaseFamilyBound_le_dyadic_power hg hg1 ht ht1
    have hw2 : 2 ≤ 2 / (gamma * theta * rho) := hv2.trans hvw
    refine ⟨hw2, ?_, hB.trans (pow_le_pow_left₀ (le_trans (by norm_num) hv2) hvw _)⟩
    rw [pow_one, show 2 / (gamma * theta * rho) = 2 / (gamma * theta) * rho⁻¹ by field_simp]
    have h1 : (1 : Real) ≤ 2 / (gamma * theta) := le_trans (by norm_num) hv2
    have hr0 : 0 ≤ rho⁻¹ := (inv_pos.mpr hr).le
    nlinarith
  refine integerPolyCoverAt_one.weaken ?_ ?_ ?_
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    obtain ⟨hw2', -, hB'⟩ := hbase gamma theta rho hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    have hw0 : (0 : Real) ≤ 2 / (gamma * theta * rho) := le_trans zero_le_two hw2'
    have hu1 : (1 : Real) ≤ uniformBase V 1 theta gamma rho :=
      le_trans one_le_two (hw2'.trans hw)
    have hmono : (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 15) ≤ uCount V D gamma theta rho := by
      unfold uCount
      exact le_max_of_le_right ((pow_le_pow_left₀ hw0 hw _).trans
        (pow_le_pow_right₀ hu1 ((show (2 : Nat) ^ 15 ≤ 2 ^ 17 by norm_num).trans hD)))
    have h : ((3 * section16BaseFamilyBound gamma theta : Nat) : Real) ≤
        (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 15) := by
      rw [Nat.cast_mul]
      exact le_pow_mono hw2' (by norm_num)
        (const_mul_le_pow (j := 2) hw2' (Nat.cast_nonneg _) (by norm_num) (Nat.cast_nonneg _) hB')
    exact h.trans hmono
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    exact (uExp_pos hV D hg hg1 ht ht1 hr hr1).1
  · intro gamma theta rho hg hg1 ht ht1 hr hr1
    obtain ⟨hw2', hri, hB'⟩ := hbase gamma theta rho hg hg1 ht ht1 hr hr1
    have hw := two_div_le_uniformBase hV hg ht hr
    have hw0 : (0 : Real) ≤ 2 / (gamma * theta * rho) := le_trans zero_le_two hw2'
    have hu1 : (1 : Real) ≤ uniformBase V 1 theta gamma rho :=
      le_trans one_le_two (hw2'.trans hw)
    have hpos : 0 < cubicBaseExponent (section16BaseFamilyBound gamma theta) rho :=
      cubicBaseExponent_pos (section16BaseFamilyBound_pos gamma theta) hr
    have hmono : (2 / (gamma * theta * rho)) ^ ((2 : Nat) ^ 17) ≤ uCount V D gamma theta rho := by
      unfold uCount
      exact le_max_of_le_right ((pow_le_pow_left₀ hw0 hw _).trans (pow_le_pow_right₀ hu1 hD))
    have h := cubicBaseExponent_inv_le hw2' (section16BaseFamilyBound_pos gamma theta) hB' hr hri
    have h' := h.trans (pow_le_pow_right₀ (le_trans one_le_two hw2')
      (show 27 + 1 * 3 + (2 : Nat) ^ 14 * 4 ≤ (2 : Nat) ^ 17 by norm_num))
    have hB := h'.trans hmono
    have := inv_anti₀ (inv_pos.mpr hpos) hB
    rw [inv_inv] at this
    exact this

theorem integerPolyCoverAt_class68 (Kc pc : Nat → Nat) (hK : ∀ k, 1 ≤ Kc k) (hp : ∀ k, 0 < pc k)
    (hlem : ∀ k, 1 ≤ k → AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    (hIntegerLemma : ∀ k, 1 ≤ k → IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor (Kc k)) (familyWidthDivisor k (pc k))))
    {l : Nat} (hl1 : 1 ≤ l) :
    IntegerPolyCoverAt l (uCount (classV Kc pc l) (uDeg68 l)) (uExp (classV Kc pc l) (uDeg68 l)) := by
  have hVl := one_le_classV Kc pc l
  rcases Nat.lt_or_ge l 2 with hl | hl
  · obtain rfl : l = 1 := by omega
    refine integerPolyCoverAt_one_uniform_low hVl ?_
    unfold uDeg68
    exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  · obtain ⟨C, hC⟩ := splitUniformClass_all_integer Kc pc hK hp hlem hIntegerLemma l hl
    have hfit := split_pair_le_uDeg68 hl
    have P0 := (C.toPower hVl).integerPolyCoverAt (C.integerCover_toPower hC hVl) (by omega) hVl (D := uDeg68 l) (by omega) (by omega)
      (by omega)
    refine P0.weaken ?_ ?_ ?_
    · intro g t s hg hg1 ht ht1 hs hs1
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]
    · intro g t s _ _ _ _ _ _
      exact (uExp_pos_le _ _ g t s).1
    · intro g t s hg hg1 ht ht1 hs hs1
      show (uCount _ _ g t s)⁻¹ ≤ _
      rw [uCount_eq hVl _ hg hg1 ht ht1 hs hs1]


end LeanProofs.GowersSzemeredi
