import OAI.Combinatorics.Progressions.Geometry.SupportedCubeEquivTransport

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem sum_overlaps {M : Type*} [AddCommMonoid M]
    (Q : Finset A) (F : A → A → M) :
    (∑ h ∈ cubeDifferenceSupport Q, ∑ x ∈ derivativeSupport Q h, F x (x + h)) =
      ∑ x ∈ Q, ∑ y ∈ Q, F x y := by
  calc
    _ = ∑ p ∈ (cubeDifferenceSupport Q ×ˢ Q).filter (fun p => p.2 + p.1 ∈ Q),
        F p.2 (p.2 + p.1) := by
      rw [Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro h _
      simp only [derivativeSupport, Finset.sum_filter]
    _ = ∑ p ∈ Q ×ˢ Q, F p.1 p.2 := by
      apply Finset.sum_bij (fun p _ => (p.2, p.2 + p.1))
      · intro p hp
        obtain ⟨hp, hsum⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_product.mpr ⟨(Finset.mem_product.mp hp).2, hsum⟩
      · intro p hp q hq he
        have hx := congrArg Prod.fst he
        have hh := congrArg Prod.snd he
        simp only at hx hh
        apply Prod.ext
        · apply add_left_cancel (a := p.2)
          exact hh.trans (congrArg (fun x => x + q.1) hx).symm
        · exact hx
      · intro p hp
        obtain ⟨hx, hy⟩ := Finset.mem_product.mp hp
        refine ⟨(p.2 - p.1, p.1), ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_product.mpr ⟨?_, hx⟩, ?_⟩
          · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
          · simpa only [add_sub_cancel] using hy
        · simp only [add_sub_cancel, Prod.eta]
      · intro p hp
        rfl
    _ = _ := Finset.sum_product Q Q (fun p => F p.1 p.2)

theorem sum_overlap_card (Q : Finset A) :
    (∑ h ∈ cubeDifferenceSupport Q, (derivativeSupport Q h).card) = Q.card ^ 2 := by
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, pow_two] using
    sum_overlaps Q (fun _ _ => (1 : ℕ))

theorem sum_overlap_weights {Q : Finset A} (hQ : Q.Nonempty) :
    (∑ h ∈ cubeDifferenceSupport Q, ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) = 1 := by
  rw [← Finset.sum_div, ← Nat.cast_sum, sum_overlap_card, Nat.cast_pow]
  exact div_self (pow_ne_zero _ (by exact_mod_cast hQ.card_pos.ne'))

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem correlation_sq_mul_card (Q : Finset A) (f u : A → ℂ) :
    (Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2 =
      ∑ h ∈ cubeDifferenceSupport Q, ((derivativeSupport Q h).card : ℝ) *
        (finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  let g := fun x => f x * star (u x)
  have hp : (∑ h ∈ cubeDifferenceSupport Q, ∑ x ∈ derivativeSupport Q h, g x * star (g (x + h))) =
      (∑ x ∈ Q, g x) * star (∑ x ∈ Q, g x) := by
    rw [sum_overlaps Q (fun x y => g x * star (g y))]
    simp only [Finset.sum_mul, Finset.mul_sum, star_sum]
    rw [Finset.sum_comm]
  have hinner (h : A) : (∑ x ∈ derivativeSupport Q h, g x * star (g (x + h))) =
      ((derivativeSupport Q h).card : ℂ) * finiteCorrelation (derivativeSupport Q h)
        (multiplicativeDerivative f h) (multiplicativeDerivative u h) := by
    rw [finiteCorrelation, Finset.card_mul_expect]
    apply Finset.sum_congr rfl
    intro x _
    simp only [g, multiplicativeDerivative, star_mul, star_star]
    ring
  have hnorm : ‖∑ x ∈ Q, g x‖ ^ 2 = (Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2 := by
    rw [← Finset.card_mul_expect Q g, norm_mul, Complex.norm_natCast, mul_pow]
    rfl
  have hreal := congrArg Complex.re hp
  simp_rw [hinner] at hreal
  rw [mul_star_re_eq_norm_sq, hnorm] at hreal
  simpa only [Complex.re_sum, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
    zero_mul, sub_zero] using hreal.symm

theorem correlation_sq_eq_sum_overlap {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) :
    ‖finiteCorrelation Q f u‖ ^ 2 =
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)).re := by
  have hcard : (Q.card : ℝ) ≠ 0 := by exact_mod_cast hQ.card_pos.ne'
  calc
    _ = ((Q.card : ℝ) ^ 2 * ‖finiteCorrelation Q f u‖ ^ 2) / (Q.card : ℝ) ^ 2 := by
      field_simp
    _ = _ := by
      rw [correlation_sq_mul_card, Finset.sum_div]
      simp only [div_mul_eq_mul_div]

theorem correlation_sq_le_sum_overlap_norm {Q : Finset A} (hQ : Q.Nonempty) (f u : A → ℂ) :
    ‖finiteCorrelation Q f u‖ ^ 2 ≤
      ∑ h ∈ cubeDifferenceSupport Q, (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        ‖finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ := by
  rw [correlation_sq_eq_sum_overlap hQ]
  apply Finset.sum_le_sum
  intro h _
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by positivity)

theorem norm_overlapCorrelation_le {Q : Finset A} (f u : A → ℂ) {B : ℝ}
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    {h : A} (hh : h ∈ cubeDifferenceSupport Q) :
    ‖finiteCorrelation (derivativeSupport Q h)
      (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ ≤ B ^ 2 := by
  apply norm_finiteCorrelation_le ((mem_cubeDifferenceSupport Q h).mp hh)
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    simpa only [multiplicativeDerivative, norm_mul, norm_star, one_mul] using
      mul_le_mul (hf x hx) (hf (x + h) hxh) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  · intro x hx
    obtain ⟨hx, hxh⟩ := Finset.mem_filter.mp hx
    have hB : 0 ≤ B := (norm_nonneg (u x)).trans (hu x hx)
    simpa only [multiplicativeDerivative, norm_mul, norm_star, pow_two] using
      mul_le_mul (hu x hx) (hu (x + h) hxh) (norm_nonneg _) hB

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem weight_large_values_of_sum {ι : Type*} (I : Finset ι) (w a : ι → ℝ)
    {r B : ℝ} (hr : 0 ≤ r) (hB : 0 < B)
    (hw : ∀ i ∈ I, 0 ≤ w i) (hsum : ∑ i ∈ I, w i = 1)
    (ha : ∀ i ∈ I, a i ≤ B) (hmean : r ≤ ∑ i ∈ I, w i * a i) :
    r / (2 * B) ≤ ∑ i ∈ I, w i * (if r / 2 ≤ a i then (1 : ℝ) else 0) := by
  classical
  have hp (i : ι) (hi : i ∈ I) : a i ≤ r / 2 + B * (if r / 2 ≤ a i then (1 : ℝ) else 0) := by
    split_ifs with h
    · simp only [mul_one]
      linarith [ha i hi]
    · simp only [mul_zero, add_zero]
      exact (lt_of_not_ge h).le
  have hbound := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hp i hi) (hw i hi))
  have he : (∑ i ∈ I, w i * (r / 2 + B * (if r / 2 ≤ a i then (1 : ℝ) else 0))) =
      r / 2 * (∑ i ∈ I, w i) + B * (∑ i ∈ I, w i * (if r / 2 ≤ a i then (1 : ℝ) else 0)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, hsum, mul_one] at hbound
  apply (div_le_iff₀ (by positivity : 0 < 2 * B)).mpr
  nlinarith

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

theorem weight_correlating_overlaps {Q : Finset A} (hQ : Q.Nonempty)
    (f u : A → ℂ) {ρ B : ℝ} (hρ : 0 ≤ ρ) (hB : 0 < B)
    (hf : ∀ x ∈ Q, ‖f x‖ ≤ 1) (hu : ∀ x ∈ Q, ‖u x‖ ≤ B)
    (hcorr : ρ ≤ ‖finiteCorrelation Q f u‖) :
    ρ ^ 2 / (2 * B ^ 2) ≤ ∑ h ∈ cubeDifferenceSupport Q,
      (((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) *
        (if ρ ^ 2 / 2 ≤ ‖finiteCorrelation (derivativeSupport Q h)
          (multiplicativeDerivative f h) (multiplicativeDerivative u h)‖ then (1 : ℝ) else 0) := by
  apply weight_large_values_of_sum _ _ _ (sq_nonneg ρ) (sq_pos_of_pos hB)
    (fun _ _ => by positivity) (sum_overlap_weights hQ)
    (fun _ hh => norm_overlapCorrelation_le f u hf hu hh)
  exact (pow_le_pow_left₀ hρ hcorr 2).trans (correlation_sq_le_sum_overlap_norm hQ f u)

theorem weight_small_overlaps {Q : Finset A} (hQ : Q.Nonempty) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∑ h ∈ (cubeDifferenceSupport Q).filter
      (fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card),
      ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2) ≤
        δ * (cubeDifferenceSupport Q).card / Q.card := by
  classical
  have hq : (0 : ℝ) < Q.card := by exact_mod_cast hQ.card_pos
  let I := (cubeDifferenceSupport Q).filter
    (fun h => ((derivativeSupport Q h).card : ℝ) ≤ δ * Q.card)
  have hp (h : A) (hh : h ∈ I) :
      ((derivativeSupport Q h).card : ℝ) / (Q.card : ℝ) ^ 2 ≤ δ / Q.card := by
    have hsmall := (Finset.mem_filter.mp hh).2
    apply (div_le_div_iff₀ (sq_pos_of_pos hq) hq).mpr
    nlinarith
  calc
    _ ≤ ∑ _h ∈ I, δ / (Q.card : ℝ) := Finset.sum_le_sum hp
    _ = (I.card : ℝ) * (δ / Q.card) := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((cubeDifferenceSupport Q).card : ℝ) * (δ / Q.card) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_filter_le _ _) (div_nonneg hδ hq.le)
    _ = _ := by ring

end Erdos3

end

end OAI
