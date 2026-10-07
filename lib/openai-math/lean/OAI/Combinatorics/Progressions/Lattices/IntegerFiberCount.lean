import Mathlib

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem card_integer_set_le_diameter_add_one (A : Finset ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |(x : ℝ) - y| ≤ L) :
    (A.card : ℝ) ≤ L + 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  have hsub : A ⊆ Finset.Icc (A.min' hA) (A.max' hA) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨A.min'_le x hx, A.le_max' x hx⟩
  have hcard : (A.card : ℝ) ≤ (A.max' hA : ℝ) + 1 - A.min' hA := by
    have hc := Finset.card_le_card hsub
    have hi := Int.card_Icc_of_le (A.min' hA) (A.max' hA)
      (le_trans (A.min'_le_max' hA) (by omega))
    have hc' : (A.card : ℤ) ≤ A.max' hA + 1 - A.min' hA := by
      exact_mod_cast hi ▸ (show (A.card : ℤ) ≤ (Finset.Icc (A.min' hA) (A.max' hA)).card by
        exact_mod_cast hc)
    exact_mod_cast hc'
  have hd := (abs_le.mp (hdiam _ (A.max'_mem hA) _ (A.min'_mem hA))).2
  linarith

theorem count_integer_phase_fibers (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η : ℝ} (hH : 0 ≤ H) (hθ : 0 < θ) (hη : 0 ≤ η)
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    (D.card : ℝ) ≤ (2 * H * θ + 2 * η + 1) * (2 * η / θ + 1) := by
  have hm (h : ℤ) (hh : h ∈ D) : |(m h : ℝ)| ≤ H * θ + η := by
    have ha := abs_le.mp (hD h hh)
    have he := abs_le.mp (hclose h hh)
    have hlo := mul_le_mul_of_nonneg_right ha.1 hθ.le
    have hhi := mul_le_mul_of_nonneg_right ha.2 hθ.le
    rw [abs_le]
    constructor <;> nlinarith only [hlo, hhi, he.1, he.2]
  have himage : ((D.image m).card : ℝ) ≤ 2 * H * θ + 2 * η + 1 := by
    apply card_integer_set_le_diameter_add_one _ (by positivity)
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hx' := abs_le.mp (hm x hx)
    have hy' := abs_le.mp (hm y hy)
    rw [abs_le]
    constructor <;> linarith
  have hfiber (a : ℤ) : ((D.filter (fun h => m h = a)).card : ℝ) ≤ 2 * η / θ + 1 := by
    apply card_integer_set_le_diameter_add_one _ (by positivity)
    intro x hx y hy
    obtain ⟨hx, hmx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hmy⟩ := Finset.mem_filter.mp hy
    have he₁ := abs_le.mp (hclose x hx)
    have he₂ := abs_le.mp (hclose y hy)
    rw [hmx] at he₁
    rw [hmy] at he₂
    apply (le_div_iff₀ hθ).mpr
    rw [← abs_of_pos hθ, ← abs_mul, abs_le]
    constructor <;> nlinarith only [he₁.1, he₁.2, he₂.1, he₂.2]
  calc
    (D.card : ℝ) = ∑ a ∈ D.image m, ((D.filter (fun h => m h = a)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    _ ≤ ∑ _a ∈ D.image m, (2 * η / θ + 1) := Finset.sum_le_sum (fun a _ => hfiber a)
    _ = ((D.image m).card : ℝ) * (2 * η / θ + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * H * θ + 2 * η + 1) * (2 * η / θ + 1) :=
      mul_le_mul_of_nonneg_right himage (by positivity)

theorem count_integer_phase_fibers_abs (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η : ℝ} (hH : 0 ≤ H) (hθ : θ ≠ 0) (hη : 0 ≤ η)
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    (D.card : ℝ) ≤ (2 * H * |θ| + 2 * η + 1) * (2 * η / |θ| + 1) := by
  rcases lt_or_gt_of_ne hθ with ht | ht
  · have he : ∀ h ∈ D, |(h : ℝ) * (-θ) - ((-m h : ℤ) : ℝ)| ≤ η := by
      intro h hh
      simpa only [Int.cast_neg, mul_neg, neg_sub_neg, abs_sub_comm] using hclose h hh
    simpa only [abs_of_neg ht] using count_integer_phase_fibers D (fun h => -m h)
      hH (neg_pos.mpr ht) hη hD he
  · simpa only [abs_of_pos ht] using count_integer_phase_fibers D m hH ht hη hD hclose

theorem small_linear_phase_of_many_near_integers (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η ρ : ℝ} (hH : 0 < H) (hρ : 0 < ρ) (hη : 0 ≤ η) (hηone : η ≤ 1)
    (hsmall : 16 * η ≤ ρ) (hθsmall : |θ| ≤ 2 * η)
    (hsize : ρ * H ≤ (D.card : ℝ))
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    |θ| ≤ 24 * η / (ρ * H) := by
  by_cases ht : θ = 0
  · rw [ht, abs_zero]
    positivity
  have hθ : 0 < |θ| := abs_pos.mpr ht
  have hc := count_integer_phase_fibers_abs D m hH.le ht hη hD hclose
  have hc' : ρ * H ≤ (2 * H * |θ| + 3) * (2 * η / |θ| + 1) := by
    apply hsize.trans (hc.trans _)
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hp := mul_le_mul_of_nonneg_right hc' hθ.le
  have hid : ((2 * H * |θ| + 3) * (2 * η / |θ| + 1)) * |θ| =
      4 * H * |θ| * η + 2 * H * |θ| ^ 2 + 6 * η + 3 * |θ| := by
    field_simp
    ring
  rw [hid] at hp
  have hsquare := mul_le_mul_of_nonneg_left hθsmall
    (show 0 ≤ 2 * H * |θ| by positivity)
  have hcost := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ H * |θ| by positivity)
  apply (le_div_iff₀ (mul_pos hρ hH)).mpr
  nlinarith only [hp, hsquare, hcost, hθsmall]

end Erdos3

end

end OAI
