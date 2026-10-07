/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Fourier.RectangularGridCharacter

namespace OAI

section

open scoped BigOperators ComplexConjugate ENNReal Real
open Finset Function MeasureTheory Set

namespace Erdos3.CircleFourier

noncomputable section

def fejerPairFrequency {N : ℕ} (p : Fin N × Fin N) : ℤ :=
  (p.1.val : ℤ) - p.2.val

def fejerFrequencies (N : ℕ) : Finset ℤ := by
  classical
  exact (Finset.univ : Finset (Fin N × Fin N)).image fejerPairFrequency

def fejerCoefficient (N : ℕ) (h : ℤ) : ℝ := by
  classical
  exact ((Finset.univ.filter fun p : Fin N × Fin N =>
    fejerPairFrequency p = h).card : ℝ) / N

def fejerPolynomial (N : ℕ) (x : Circle) : ℝ :=
  (∑ h ∈ fejerFrequencies N,
    (fejerCoefficient N h : ℂ) * character (h • x)).re

private lemma fejer_grouped (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (∑ p ∈ (Finset.univ.filter fun p : Fin N × Fin N =>
          fejerPairFrequency p = h), character (fejerPairFrequency p • x)) =
      ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) := by
  classical
  rw [Finset.sum_fiberwise_eq_sum_filter]
  rw [Finset.filter_eq_self.2]
  intro p hp
  simp only [fejerFrequencies, Finset.mem_image]
  exact ⟨p, Finset.mem_univ _, rfl⟩

private lemma fejer_pair_sum_eq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (∑ j : Fin N, character ((j.val : ℤ) • x)) *
        (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) := by
  calc
    _ = ∑ j : Fin N, ∑ k : Fin N,
        character (fejerPairFrequency (j, k) • x) := by
      exact Fintype.sum_prod_type (γ := ℂ)
        (fun p : Fin N × Fin N => character (fejerPairFrequency p • x))
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [← character_add]
      congr 2
      simp only [fejerPairFrequency, sub_eq_add_neg, add_smul]

private lemma fejer_neg_sum_eq_conj (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
      star (∑ k : Fin N, character ((k.val : ℤ) • x)) := by
  change (∑ k : Fin N, character ((-(k.val : ℤ)) • x)) =
    (starRingEnd ℂ) (∑ k : Fin N, character ((k.val : ℤ) • x))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  change AddCircle.toCircle ((-(k.val : ℤ)) • x) =
    (starRingEnd ℂ) (AddCircle.toCircle ((k.val : ℤ) • x))
  rw [neg_smul, AddCircle.toCircle_neg]
  exact _root_.Circle.coe_inv_eq_conj _

private lemma fejer_fin_sum_eq_geo (N : ℕ) (x : Circle) :
    (∑ k : Fin N, character ((k.val : ℤ) • x)) =
      geometricCharacterSum N x := by
  rw [geometricCharacterSum_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro k hk
  rw [natCast_zsmul]

private lemma fejer_pair_sum_eq_norm_sq (N : ℕ) (x : Circle) :
    ∑ p : Fin N × Fin N, character (fejerPairFrequency p • x) =
      (‖geometricCharacterSum N x‖ ^ 2 : ℝ) := by
  rw [fejer_pair_sum_eq, fejer_neg_sum_eq_conj, fejer_fin_sum_eq_geo]
  change geometricCharacterSum N x *
    (starRingEnd ℂ) (geometricCharacterSum N x) = _
  rw [Complex.mul_conj]
  norm_cast
  exact Complex.sq_norm _ |>.symm

lemma complex_fejerPolynomial_eq (N : ℕ) (x : Circle) :
    ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x) =
      ((‖geometricCharacterSum N x‖ ^ 2 / N : ℝ) : ℂ) := by
  classical
  rw [Complex.ofReal_div]
  push_cast
  have hpair := fejer_pair_sum_eq_norm_sq N x
  rw [← Complex.ofReal_pow, ← hpair, ← fejer_grouped N x, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro h hh
  rw [fejerCoefficient, Complex.ofReal_div]
  push_cast
  rw [div_mul_eq_mul_div]
  congr 1
  calc
    (#{p : Fin N × Fin N | fejerPairFrequency p = h} : ℂ) *
        character (h • x) =
        ∑ p with fejerPairFrequency p = h, character (h • x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ p with fejerPairFrequency p = h,
        character (fejerPairFrequency p • x) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]

lemma fejerPolynomial_eq (N : ℕ) (x : Circle) :
    fejerPolynomial N x = ‖geometricCharacterSum N x‖ ^ 2 / N := by
  have h := congrArg Complex.re (complex_fejerPolynomial_eq N x)
  simpa only [fejerPolynomial, Complex.ofReal_re] using h

lemma fejerPolynomial_nonneg (N : ℕ) (x : Circle) :
    0 ≤ fejerPolynomial N x := by
  rw [fejerPolynomial_eq]
  positivity

lemma fejerPolynomial_le_of_distance {N : ℕ} (hN : 0 < N)
    {η : ℝ} (hη : 0 < η) {x : Circle} (hx : η ≤ integerDistance x) :
    fejerPolynomial N x ≤ 1 / (4 * N * η ^ 2) := by
  rw [fejerPolynomial_eq]
  have hgeom :=
    two_mul_integerDistance_mul_norm_geometricCharacterSum_le_one N x
  have hnorm := norm_nonneg (geometricCharacterSum N x)
  have hdist := integerDistance_nonneg x
  have hbound : 2 * η * ‖geometricCharacterSum N x‖ ≤ 1 := by nlinarith
  have hsquare : 4 * η ^ 2 * ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 := by
    have hs := mul_self_le_mul_self (mul_nonneg (by positivity) hnorm) hbound
    nlinarith
  have hn2 : ‖geometricCharacterSum N x‖ ^ 2 ≤ 1 / (4 * η ^ 2) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * η ^ 2)]
    nlinarith
  calc
    ‖geometricCharacterSum N x‖ ^ 2 / (N : ℝ) ≤
        (1 / (4 * η ^ 2)) / N := by gcongr
    _ = 1 / (4 * N * η ^ 2) := by field_simp

private lemma integral_character (h : ℤ) :
    ∫ x : Circle, character (h • x) ∂circleHaar = if h = 0 then 1 else 0 := by
  by_cases hh : h = 0
  · subst h
    simp
  · simp only [hh, ↓reduceIte]
    exact integral_eq_zero_of_add_right_eq_neg (μ := circleHaar)
      (fourier_add_half_inv_index hh (by norm_num))

lemma integral_fejerPolynomial {N : ℕ} (hN : 0 < N) :
    ∫ x : Circle, fejerPolynomial N x ∂circleHaar = 1 := by
  simp_rw [fejerPolynomial]
  have hterm : ∀ h ∈ fejerFrequencies N,
      Integrable (fun x : Circle =>
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    intro h hh
    apply Integrable.const_mul
    apply Integrable.of_bound (fourier h).continuous.aestronglyMeasurable 1
    exact ae_of_all _ fun x => (norm_character (h • x)).le
  have hint : Integrable (fun x : Circle =>
      ∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)) circleHaar := by
    have hi := integrable_finsetSum' (fejerFrequencies N) hterm
    have heq : (∑ h ∈ fejerFrequencies N,
        fun x : Circle => (fejerCoefficient N h : ℂ) * character (h • x)) =
        fun x : Circle => ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) := by
      funext x
      exact Finset.sum_apply x (fejerFrequencies N) _
    rw [← heq]
    exact hi
  calc
    (∫ x : Circle, (∑ h ∈ fejerFrequencies N,
        (fejerCoefficient N h : ℂ) * character (h • x)).re ∂circleHaar) =
        (∫ x : Circle, ∑ h ∈ fejerFrequencies N,
          (fejerCoefficient N h : ℂ) * character (h • x) ∂circleHaar).re :=
      integral_re hint
    _ = 1 := by
      rw [integral_finsetSum (fejerFrequencies N) hterm]
      simp_rw [integral_const_mul, integral_character]
      rw [Finset.sum_eq_single 0]
      · rw [ite_eq_left rfl, mul_one]
        unfold fejerCoefficient fejerPairFrequency
        have hdiag : (Finset.univ.filter fun p : Fin N × Fin N =>
            (p.1.val : ℤ) - p.2.val = 0).card = N := by
          rw [show (Finset.univ.filter fun p : Fin N × Fin N =>
              (p.1.val : ℤ) - p.2.val = 0) =
              Finset.univ.image (fun j : Fin N => (j, j)) by
            ext p
            simp only [Finset.mem_filter, Finset.mem_univ, true_and,
              Finset.mem_image]
            constructor
            · intro hp
              have : p.1 = p.2 := by
                apply Fin.ext
                omega
              exact ⟨p.1, by ext <;> simp [this]⟩
            · rintro ⟨j, -, rfl⟩
              simp]
          calc
            (Finset.univ.image (fun j : Fin N => (j, j))).card =
                (Finset.univ : Finset (Fin N)).card :=
              Finset.card_image_of_injective _ fun i j h => by
                simpa using congrArg Prod.fst h
            _ = N := by simp
        rw [hdiag, div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN))]
        norm_num
      · intro h hh hne
        rw [ite_eq_right hne, mul_zero]
      · intro hz
        exfalso
        apply hz
        unfold fejerFrequencies
        apply Finset.mem_image.2
        exact ⟨(⟨0, hN⟩, ⟨0, hN⟩), Finset.mem_univ _,
          by simp [fejerPairFrequency]⟩

private lemma fejer_fiber_card_le (N : ℕ) (h : ℤ) :
    (Finset.univ.filter fun p : Fin N × Fin N =>
      fejerPairFrequency p = h).card ≤ N := by
  let s := Finset.univ.filter fun p : Fin N × Fin N => fejerPairFrequency p = h
  calc
    s.card ≤ (Finset.univ : Finset (Fin N)).card := by
      apply Finset.card_le_card_of_injOn Prod.fst
      · intro p hp
        exact Finset.mem_univ _
      · intro p hp q hq hpq
        apply Prod.ext hpq
        apply Fin.ext
        have hpf := (Finset.mem_filter.mp hp).2
        have hqf := (Finset.mem_filter.mp hq).2
        unfold fejerPairFrequency at hpf hqf
        omega
    _ = N := by simp

lemma fejerCoefficient_nonneg (N : ℕ) (h : ℤ) :
    0 ≤ fejerCoefficient N h := by
  unfold fejerCoefficient
  positivity

lemma fejerCoefficient_le_one {N : ℕ} (hN : 0 < N) (h : ℤ) :
    fejerCoefficient N h ≤ 1 := by
  unfold fejerCoefficient
  rw [div_le_one (Nat.cast_pos.mpr hN)]
  exact_mod_cast fejer_fiber_card_le N h

lemma continuous_fejerPolynomial (N : ℕ) : Continuous (fejerPolynomial N) := by
  rw [show fejerPolynomial N = fun x =>
      ‖geometricCharacterSum N x‖ ^ 2 / N by
    funext x
    exact fejerPolynomial_eq N x]
  apply Continuous.div_const
  apply Continuous.pow
  apply Continuous.norm
  unfold geometricCharacterSum
  apply continuous_finsetSum
  intro n hn
  unfold character
  exact continuous_subtype_val.comp
    (AddCircle.continuous_toCircle.comp (continuous_nsmul n))

lemma norm_geometricCharacterSum_le_card (N : ℕ) (x : Circle) :
    ‖geometricCharacterSum N x‖ ≤ N := by
  unfold geometricCharacterSum
  calc
    ‖∑ n ∈ range N, character (n • x)‖ ≤
        ∑ n ∈ range N, ‖character (n • x)‖ := norm_sum_le _ _
    _ = N := by simp

lemma fejerPolynomial_le_card (N : ℕ) (x : Circle) :
    fejerPolynomial N x ≤ N := by
  rw [fejerPolynomial_eq]
  by_cases hN : N = 0
  · simp [hN]
  · rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))]
    have h := norm_geometricCharacterSum_le_card N x
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) h

lemma integrable_fejerPolynomial_comp_sub (N : ℕ) (x : Circle) :
    Integrable (fun y : Circle => fejerPolynomial N (x - y)) circleHaar := by
  apply Integrable.of_bound
    ((continuous_fejerPolynomial N).comp
      (continuous_const.sub continuous_id)).aestronglyMeasurable N
  exact ae_of_all _ fun y => by
    change |fejerPolynomial N (x - y)| ≤ (N : ℝ)
    rw [abs_of_nonneg (fejerPolynomial_nonneg N _)]
    exact fejerPolynomial_le_card N _

lemma fejerPolynomial_neg (N : ℕ) (x : Circle) :
    fejerPolynomial N (-x) = fejerPolynomial N x := by
  rw [fejerPolynomial_eq, fejerPolynomial_eq]
  congr 2
  unfold geometricCharacterSum
  calc
    ‖∑ n ∈ range N, character (n • -x)‖ =
        ‖star (∑ n ∈ range N, character (n • x))‖ := by
      congr 1
      change _ = (starRingEnd ℂ) _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro n hn
      rw [smul_neg, character_neg]
      rfl
    _ = _ := Complex.norm_conj _

lemma integral_fejerPolynomial_comp_sub {N : ℕ} (hN : 0 < N) (x : Circle) :
    ∫ y : Circle, fejerPolynomial N (x - y) ∂circleHaar = 1 := by
  calc
    ∫ y : Circle, fejerPolynomial N (x - y) ∂circleHaar =
        ∫ y : Circle, fejerPolynomial N (y-x) ∂circleHaar := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show x-y = -(y-x) by abel, fejerPolynomial_neg]
    _ = ∫ y : Circle, fejerPolynomial N y ∂circleHaar := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fejerPolynomial N) (-x)
    _ = 1 := integral_fejerPolynomial hN

end
end Erdos3.CircleFourier

end

end OAI
