import OAI.Combinatorics.Progressions.Estimates.WeightedRudin
import OAI.Combinatorics.Progressions.Probability.MassConvolution

namespace OAI

section

open Finset
open scoped BigOperators

namespace Erdos3

noncomputable def realFinsetIndicator {G : Type*} (A : Finset G) (x : G) : ℝ := by
  classical
  exact if x ∈ A then 1 else 0

namespace RelativeSpectrumBridge

variable {G : Type*} [Fintype G] [AddCommGroup G]

omit [AddCommGroup G] in

theorem sum_realFinsetIndicator_mul_eq_const_mul_card
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) :
    ∑ x : G, realFinsetIndicator X x * w x = c * X.card := by
  classical
  calc
    ∑ x : G, realFinsetIndicator X x * w x = ∑ x ∈ X, c := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realFinsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [realFinsetIndicator, hxX]
    _ = c * X.card := by simp [mul_comm]

theorem sum_realFinsetIndicator_mul_character_eq_const_mul
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (psi : AddChar G ℂ) :
    ∑ x : G, ((realFinsetIndicator X x * w x : ℝ) : ℂ) * psi x =
      (c : ℂ) * Chang.spectrumSum X psi := by
  classical
  calc
    ∑ x : G, ((realFinsetIndicator X x * w x : ℝ) : ℂ) * psi x =
        ∑ x ∈ X, (c : ℂ) * psi x := by
      rw [← Finset.sum_subset (s₁ := X) (s₂ := Finset.univ)]
      · apply Finset.sum_congr rfl
        intro x hx
        simp [realFinsetIndicator, hx, hw x (hXB hx)]
      · simp
      · intro x hxU hxX
        simp [realFinsetIndicator, hxX]
    _ = (c : ℂ) * Chang.spectrumSum X psi := by
      rw [Chang.spectrumSum, Finset.mul_sum]

theorem mem_relativeLargeSpectrum_of_eq_const_iff
    {B X : Finset G} (hXB : X ⊆ B) {w : G → ℝ} {c : ℝ}
    (hw : ∀ x ∈ B, w x = c) (hc : 0 < c)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ RelativeChangSanders.relativeLargeSpectrum w (realFinsetIndicator X) eta ↔
      psi ∈ Chang.largeSpectrum X eta := by
  classical
  rw [RelativeChangSanders.mem_relativeLargeSpectrum, Chang.mem_largeSpectrum]
  rw [sum_realFinsetIndicator_mul_eq_const_mul_card hXB hw]
  rw [sum_realFinsetIndicator_mul_character_eq_const_mul hXB hw]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  constructor
  · intro h
    have hh : c * (eta * (X.card : ℝ)) ≤
        c * ‖Chang.spectrumSum X psi‖ := by
      calc
        c * (eta * (X.card : ℝ)) = eta * (c * (X.card : ℝ)) := by ring
        _ ≤ c * ‖Chang.spectrumSum X psi‖ := h
    nlinarith
  · intro h
    calc
      eta * (c * (X.card : ℝ)) = c * (eta * (X.card : ℝ)) := by ring
      _ ≤ c * ‖Chang.spectrumSum X psi‖ :=
        mul_le_mul_of_nonneg_left h hc.le

end RelativeSpectrumBridge
end Erdos3

end

section

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem card_weightedDissociated_relativeLargeSpectrum_le
    (mu f : G → ℝ) (K eta : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1)
    (heta : 0 < eta)
    (hDelta : IsWeightedDissociated mu K Delta)
    (hsub : Delta ⊆ relativeLargeSpectrum mu f eta)
    (hmass : 0 < ∑ x : G, f x * mu x) :
    (Delta.card : ℝ) ≤
      2 * (K + log ((∑ x : G, f x * mu x)⁻¹)) / eta ^ 2 := by
  let a : ℝ := ∑ x : G, f x * mu x
  have ha : 0 < a := by simpa [a] using hmass
  let spec : AddChar G ℂ → ℂ := fun psi ↦
    ∑ x : G, (f x * mu x : ℝ) * psi x
  choose u hu huspec using fun psi : AddChar G ℂ ↦
    Complex.exists_norm_eq_mul_self (spec psi)
  let c : AddChar G ℂ → ℂ := fun psi ↦ (eta : ℂ) * u psi
  let P : G → ℝ := fun x ↦ (∑ psi ∈ Delta, c psi * psi x).re
  have hc_norm (psi : AddChar G ℂ) : ‖c psi‖ ^ 2 = eta ^ 2 := by
    simp [c, hu, abs_of_pos heta]
  have hc_sq : ∑ psi ∈ Delta, ‖c psi‖ ^ 2 = eta ^ 2 * Delta.card := by
    simp_rw [hc_norm]
    simp
    ring
  have hcomplex :
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
        (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
    calc
      ∑ x : G, ((f x * mu x : ℝ) : ℂ) *
          (∑ psi ∈ Delta, c psi * psi x) =
          ∑ psi ∈ Delta,
            c psi * ∑ x : G, ((f x * mu x : ℝ) : ℂ) * psi x := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro psi hpsi
        apply sum_congr rfl
        intro x hx
        ring
      _ = ∑ psi ∈ Delta, (eta : ℂ) * (‖spec psi‖ : ℂ) := by
        apply sum_congr rfl
        intro psi hpsi
        dsimp [c, spec]
        rw [mul_assoc, ← huspec]
      _ = (eta : ℂ) * ∑ psi ∈ Delta, (‖spec psi‖ : ℂ) := by
        rw [Finset.mul_sum]
  have hmeanP :
      ∑ x : G, f x * mu x * P x =
        eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
    have hre := congrArg Complex.re hcomplex
    calc
      ∑ x : G, f x * mu x * P x =
          (∑ x : G, ((f x * mu x : ℝ) : ℂ) *
            (∑ psi ∈ Delta, c psi * psi x)).re := by
        simp [P, Complex.re_sum, Complex.mul_re]
      _ = ((eta : ℂ) *
          ∑ psi ∈ Delta, (‖spec psi‖ : ℂ)).re := hre
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by simp
  have hmean_lower :
      eta ^ 2 * a * Delta.card ≤ ∑ x : G, f x * mu x * P x := by
    rw [hmeanP]
    calc
      eta ^ 2 * a * (Delta.card : ℝ) =
          ∑ psi ∈ Delta, eta * (eta * a) := by
        simp
        ring
      _ ≤ ∑ psi ∈ Delta, eta * ‖spec psi‖ := by
        gcongr with psi hpsi
        have hs := mem_relativeLargeSpectrum.mp (hsub hpsi)
        simpa [a, spec] using hs
      _ = eta * ∑ psi ∈ Delta, ‖spec psi‖ := by
        rw [Finset.mul_sum]
  let w : G → ℝ := fun x ↦ f x * mu x / a
  have hw0 : ∀ x, 0 ≤ w x := by
    intro x
    exact div_nonneg (mul_nonneg (hf0 x) (hmu x)) ha.le
  have hw_sum : ∑ x : G, w x = 1 := by
    dsimp [w]
    rw [← Finset.sum_div]
    dsimp [a]
    exact div_self ha.ne'
  have hmean_w : eta ^ 2 * Delta.card ≤ ∑ x : G, w x * P x := by
    calc
      eta ^ 2 * (Delta.card : ℝ) ≤
          (∑ x : G, f x * mu x * P x) / a := by
        rw [le_div_iff₀ ha]
        calc
          eta ^ 2 * (Delta.card : ℝ) * a =
              eta ^ 2 * a * (Delta.card : ℝ) := by ring
          _ ≤ _ := hmean_lower
      _ = ∑ x : G, w x * P x := by
        dsimp [w]
        rw [Finset.sum_div]
        apply sum_congr rfl
        intro x hx
        ring
  have hJensen :
      exp (eta ^ 2 * Delta.card) ≤
        ∑ x : G, w x * exp (P x) := by
    calc
      exp (eta ^ 2 * Delta.card) ≤ exp (∑ x : G, w x * P x) := by
        exact Real.exp_le_exp.mpr hmean_w
      _ ≤ _ := exp_weightedAverage_le_weightedAverage_exp w hw0 hw_sum P
  have hweighted_le :
      ∑ x : G, w x * exp (P x) ≤
        a⁻¹ * ∑ x : G, mu x * exp (P x) := by
    dsimp [w]
    rw [Finset.mul_sum]
    apply sum_le_sum
    intro x hx
    rw [div_eq_inv_mul]
    calc
      a⁻¹ * (f x * mu x) * exp (P x) ≤
          a⁻¹ * (1 * mu x) * exp (P x) := by
        apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ha.le)
        exact mul_le_mul_of_nonneg_right (hf1 x) (hmu x)
      _ = a⁻¹ * (mu x * exp (P x)) := by ring
  have hRudin :
      ∑ x : G, mu x * exp (P x) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    have hr := weighted_rudin_exp_ineq mu K Delta hmu hDelta c
    simpa [P, hc_sq] using hr
  have hchain :
      exp (eta ^ 2 * Delta.card) ≤
        a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2) :=
    hJensen.trans (hweighted_le.trans
      (mul_le_mul_of_nonneg_left hRudin (inv_nonneg.mpr ha.le)))
  have hmul :
      a * exp (eta ^ 2 * Delta.card) ≤
        exp (K + eta ^ 2 * Delta.card / 2) := by
    calc
      a * exp (eta ^ 2 * Delta.card) ≤
          a * (a⁻¹ * exp (K + eta ^ 2 * Delta.card / 2)) := by
        gcongr
      _ = exp (K + eta ^ 2 * Delta.card / 2) := by
        field_simp
  have hlinear :
      log a + eta ^ 2 * Delta.card ≤
        K + eta ^ 2 * Delta.card / 2 := by
    rw [← exp_log ha, ← exp_add] at hmul
    exact Real.exp_le_exp.mp hmul
  have heta_sq : 0 < eta ^ 2 := sq_pos_of_pos heta
  rw [le_div_iff₀ heta_sq]
  rw [log_inv]
  nlinarith

theorem card_weightedDissociated_realFinsetIndicator_le
    (B X : Finset G) (hXB : X ⊆ B) (hX : X.Nonempty)
    (w : G → ℝ) (c R eta : ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∈ B, w x = c)
    (hc : 0 < c) (hR : (c * X.card)⁻¹ ≤ R)
    (heta : 0 < eta) (Delta : Finset (AddChar G ℂ))
    (hDelta : IsWeightedDissociated w 1 Delta)
    (hsub : Delta ⊆ Chang.largeSpectrum X eta) :
    (Delta.card : ℝ) ≤ 2 * (1 + log R) / eta ^ 2 := by
  classical
  have hmass_eq :
      ∑ x : G, realFinsetIndicator X x * w x = c * X.card :=
    RelativeSpectrumBridge.sum_realFinsetIndicator_mul_eq_const_mul_card hXB hw
  have hmass : 0 < ∑ x : G, realFinsetIndicator X x * w x := by
    rw [hmass_eq]
    have hXcard : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    positivity
  have hsub' : Delta ⊆
      relativeLargeSpectrum w (realFinsetIndicator X) eta := by
    intro psi hpsi
    exact (RelativeSpectrumBridge.mem_relativeLargeSpectrum_of_eq_const_iff
      hXB hw hc eta psi).2 (hsub hpsi)
  have hdim := card_weightedDissociated_relativeLargeSpectrum_le
    w (realFinsetIndicator X) 1 eta Delta hw0
    (by intro x; unfold realFinsetIndicator; split <;> norm_num)
    (by intro x; unfold realFinsetIndicator; split <;> norm_num)
    heta hDelta hsub' hmass
  have hmassInv :
      ((∑ x : G, realFinsetIndicator X x * w x)⁻¹) ≤ R := by
    simpa [hmass_eq] using hR
  have hlog :
      log ((∑ x : G, realFinsetIndicator X x * w x)⁻¹) ≤ log R :=
    Real.log_le_log (inv_pos.mpr hmass) hmassInv
  calc
    (Delta.card : ℝ) ≤
        2 * (1 + log ((∑ x : G, realFinsetIndicator X x * w x)⁻¹)) /
          eta ^ 2 := by simpa using hdim
    _ ≤ 2 * (1 + log R) / eta ^ 2 := by
      gcongr

end Erdos3.RelativeChangSanders

end

end

end OAI
