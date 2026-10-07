/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.CyclicMixedReflection
import OAI.Combinatorics.Progressions.Estimates.NativeProductVerticalization
import OAI.Combinatorics.Progressions.Estimates.QuadraticAntisymmetricCorrelation
import OAI.Combinatorics.Progressions.Fourier.QuadraticLocalFrequency
import OAI.Combinatorics.Progressions.Polynomial.NativeZeroDegreeCorrelation

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_reflected_corner_correlation (F : G → G → ℂ) (b₁ b₂ b₃ : G → ℂ)
    (hb₁ : ∀ x, ‖b₁ x‖ ≤ 1) (hb₂ : ∀ y, ‖b₂ y‖ ≤ 1) (hb₃ : ∀ z, ‖b₃ z‖ ≤ 1)
    {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hcorr : ρ ≤ (𝔼 x, 𝔼 y, F y x * b₁ x * b₂ y * b₃ (x + y)).re) :
    ∃ (z : G) (b : G → ℂ), (∀ y, ‖b y‖ ≤ 1) ∧
      ρ ^ 2 ≤ (𝔼 y, 𝔼 y',
        F y (z - y - y') * star (F y' (z - y - y')) * b y * star (b y')).re := by
  let B (z y : G) := b₂ y * star (b₃ (z - y))
  have hnorm : ρ ≤ ‖𝔼 x, b₁ x * (𝔼 y, F y x * b₂ y * b₃ (x + y))‖ := by
    have heq : (𝔼 x, b₁ x * (𝔼 y, F y x * b₂ y * b₃ (x + y))) =
        𝔼 x, 𝔼 y, F y x * b₁ x * b₂ y * b₃ (x + y) := by
      simp_rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      ring
    rw [heq]
    exact hcorr.trans (Complex.re_le_norm _)
  have hcs := finite_family_cauchy_schwarz_re b₁
    (fun y x => F y x * b₂ y * b₃ (x + y)) hb₁
  simp only [one_pow, one_mul] at hcs
  have hchange : (𝔼 y, 𝔼 y', 𝔼 x,
      (F y x * b₂ y * b₃ (x + y)) * star (F y' x * b₂ y' * b₃ (x + y'))) =
      𝔼 z, 𝔼 y, 𝔼 y',
        F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
    calc
      _ = 𝔼 y, 𝔼 y', 𝔼 z,
          F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro y' _
        apply Fintype.expect_equiv (Equiv.addRight (y + y'))
        intro x
        have h₁ : x + (y + y') - y = x + y' := by abel
        have h₂ : x + (y + y') - y' = x + y := by abel
        simp only [Equiv.coe_addRight, B, h₁, h₂, add_sub_cancel_right, star_mul, star_star]
        ring
      _ = 𝔼 y, 𝔼 z, 𝔼 y',
          F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y') := by
        apply Finset.expect_congr rfl
        intro y _
        exact Finset.expect_comm _ _ _
      _ = _ := Finset.expect_comm _ _ _
  have hmean := (pow_le_pow_left₀ hρ hnorm 2).trans hcs
  rw [hchange, expect_re, Fintype.expect_eq_sum_div_card] at hmean
  have hsum : (∑ _z : G, ρ ^ 2) ≤ ∑ z : G, (𝔼 y, 𝔼 y',
      F y (z - y - y') * star (F y' (z - y - y')) * B z y * star (B z y')).re := by
    have hcard : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using
      (le_div_iff₀ hcard).mp hmean
  obtain ⟨z, _, hz⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  refine ⟨z, B z, ?_, hz⟩
  intro y
  simp only [B, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hb₂ _)).trans (hb₃ _)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem derivative_correlation_mean_sq_le (f : G → ℂ) (g : G → G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖𝔼 h, 𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ ^ 2 ≤
      (𝔼 a, 𝔼 x, multiplicativeDerivative f a x *
        (𝔼 h, star (g h x) * g (h - a) (x + a))).re := by
  have hmove (h : G) : (𝔼 x, multiplicativeDerivative f h x * star (g h x)) =
      𝔼 y, star (f y) * (f (y - h) * star (g h (y - h))) := by
    apply Fintype.expect_equiv (Equiv.addRight h)
    intro x
    simp only [Equiv.coe_addRight, add_sub_cancel_right, multiplicativeDerivative]
    ring
  have havg : (𝔼 h, 𝔼 x, multiplicativeDerivative f h x * star (g h x)) =
      𝔼 y, star (f y) * (𝔼 h, f (y - h) * star (g h (y - h))) := by
    simp_rw [hmove]
    rw [Finset.expect_comm]
    apply Finset.expect_congr rfl
    intro y _
    exact (Finset.mul_expect _ _ _).symm
  have hcross : (𝔼 h, 𝔼 k, 𝔼 y,
      (f (y - h) * star (g h (y - h))) * star (f (y - k) * star (g k (y - k)))) =
      𝔼 a, 𝔼 x, multiplicativeDerivative f a x *
        (𝔼 h, star (g h x) * g (h - a) (x + a)) := by
    calc
      _ = 𝔼 h, 𝔼 k, 𝔼 x, multiplicativeDerivative f (h - k) x *
          (star (g h x) * g k (x + (h - k))) := by
        apply Finset.expect_congr rfl
        intro h _
        apply Finset.expect_congr rfl
        intro k _
        symm
        apply Fintype.expect_equiv (Equiv.addRight h)
        intro x
        simp only [Equiv.coe_addRight, add_sub_cancel_right, star_mul, star_star,
          multiplicativeDerivative, ← add_sub_assoc]
        ring
      _ = 𝔼 h, 𝔼 a, 𝔼 x, multiplicativeDerivative f a x *
          (star (g h x) * g (h - a) (x + a)) := by
        apply Finset.expect_congr rfl
        intro h _
        apply Fintype.expect_equiv (Equiv.subLeft h)
        intro k
        simp only [Equiv.subLeft_apply, sub_sub_cancel]
      _ = _ := by
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro a _
        rw [Finset.expect_comm]
        apply Finset.expect_congr rfl
        intro x _
        exact (Finset.mul_expect _ _ _).symm
  have hcs := finite_family_cauchy_schwarz_re (fun y => star (f y))
    (fun h y => f (y - h) * star (g h (y - h)))
    (M := 1) (fun y => by simpa only [norm_star] using hf y)
  rw [havg]
  simpa only [one_pow, one_mul, hcross] using hcs

theorem derivative_correlation_fourth_moment (f : G → ℂ) (g : G → G → ℂ)
    (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖𝔼 h, 𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ ^ 4 ≤
      (𝔼 a, 𝔼 h, 𝔼 k, 𝔼 x,
        star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))).re := by
  let T (a : G) := 𝔼 x, multiplicativeDerivative f a x *
    (𝔼 h, star (g h x) * g (h - a) (x + a))
  have hfirst : ‖𝔼 h, 𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ ^ 2 ≤
      ‖𝔼 a, T a‖ := (derivative_correlation_mean_sq_le f g hf).trans (Complex.re_le_norm _)
  have hsecond (a : G) : ‖T a‖ ^ 2 ≤
      (𝔼 h, 𝔼 k, 𝔼 x,
        star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))).re := by
    have hcs := finite_family_cauchy_schwarz_re (multiplicativeDerivative f a)
      (fun h x => star (g h x) * g (h - a) (x + a))
      (M := 1) (multiplicativeDerivative_norm_le_one f hf a)
    simpa only [T, one_pow, one_mul, star_mul, star_star, mul_assoc, mul_comm, mul_left_comm] using hcs
  calc
    _ = (‖𝔼 h, 𝔼 x, multiplicativeDerivative f h x * star (g h x)‖ ^ 2) ^ 2 := by ring
    _ ≤ ‖𝔼 a, T a‖ ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
    _ ≤ 𝔼 a, ‖T a‖ ^ 2 := norm_expect_sq_le_expect_norm_sq T
    _ ≤ _ := by
      rw [expect_re]
      exact Finset.expect_le_expect (fun a _ => hsecond a)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem exists_phase_aligned_derivatives (f : G → ℂ) (g : G → G → ℂ) :
    ∃ c : G → ℂ, (∀ h, ‖c h‖ = 1) ∧
      (𝔼 h, 𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) =
        ((𝔼 h, ‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖ : ℝ) : ℂ) := by
  choose c hc hphase using fun h =>
    exists_complex_unit_phase (𝔼 n, multiplicativeDerivative f h n * star (g h n))
  refine ⟨c, hc, ?_⟩
  have heq (h : G) : (𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) =
      (‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖ : ℂ) := by
    rw [← hphase h, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    simp only [star_mul, star_star]
    ring
  simp_rw [heq]
  simp [Fintype.expect_eq_sum_div_card]

theorem exists_correlated_corner (f : G → ℂ) (g : G → G → ℂ)
    (hf : ∀ n, ‖f n‖ ≤ 1) {ρ : ℝ}
    (hcorr : ρ ≤ 𝔼 h, ‖𝔼 n, multiplicativeDerivative f h n * star (g h n)‖) :
    ∃ b₁ b₂ b₃ : G → ℂ,
      (∀ x, ‖b₁ x‖ ≤ 1) ∧ (∀ y, ‖b₂ y‖ ≤ 1) ∧ (∀ z, ‖b₃ z‖ ≤ 1) ∧
      ρ ≤ (𝔼 x, 𝔼 y, g y x * b₁ x * b₂ y * b₃ (x + y)).re := by
  obtain ⟨c, hc, hphase⟩ := exists_phase_aligned_derivatives f g
  refine ⟨(fun x => star (f x)), (fun y => star (c y)), f, ?_, ?_, hf, ?_⟩
  · intro x
    simpa only [norm_star] using hf x
  · intro y
    simp only [norm_star, hc, le_refl]
  · have heq : (𝔼 x, 𝔼 y, g y x * star (f x) * star (c y) * f (x + y)) =
        star (𝔼 h, 𝔼 n, multiplicativeDerivative f h n * star (star (c h) * g h n)) := by
      calc
        _ = 𝔼 y, 𝔼 x, star (multiplicativeDerivative f y x * star (star (c y) * g y x)) := by
          rw [Finset.expect_comm]
          apply Finset.expect_congr rfl
          intro y _
          apply Finset.expect_congr rfl
          intro x _
          simp only [multiplicativeDerivative, star_mul, star_star]
          ring
        _ = _ := by simp only [expect_star]
    rw [heq, hphase]
    simpa only [Complex.star_def, Complex.conj_re, Complex.ofReal_re] using hcorr

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_bounded_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ F : NativeBoundedMultidegreeFamily (mixedCorrelationDegree 1) (Fin 1 × Unit) ((p + C) ^ C),
          ∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
              star (F.eval (0, ()) (correlationInput (h.val : ℤ) (n.val : ℤ)))‖ := by
  obtain ⟨A, _, hfrequency⟩ := exists_quadratic_local_frequency
  obtain ⟨B, _, hfamily⟩ := exists_quadratic_bounded_family
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + 1 + (Q + 1 + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : q + 1 + (q + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q + 1 ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 1 + B) ^ B := by positivity
    linarith
  have hfamilyC : (q + 1 + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, r, u, c, b, a, h₀, hr, _, _, _, hcorr⟩ := hfrequency hp f hf hG
  obtain ⟨F, hF⟩ := hfamily (show 1 ≤ q + 1 by linarith) r (by linarith : (r : ℝ) ≤ q + 1)
    a b u c h₀
  refine ⟨H, hH, ?_, F.mono hfamilyC, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -q))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨hsmall, hc⟩ := hcorr h hh
    have hvalue (n : ZMod N) : F.eval (0, ()) (correlationInput (h.val : ℤ) (n.val : ℤ)) =
        CircleFourier.character (((n.val : ℝ) *
          (a + ∑ i, affineCyclicTorusLocalLift u c h₀ h i * b i) : ℝ) : CircleFourier.Circle) / 2 := by
      simpa only [Int.cast_natCast] using
        hF h (fun i => (hsmall i).trans (by norm_num)) (n.val : ℤ)
    simp only [NativeBoundedMultidegreeFamily.mono_eval, hvalue, star_div₀, star_ofNat,
      ← mul_div_assoc, ← Finset.expect_div, norm_div, Complex.norm_ofNat]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -q - 1)).trans
      ((exp_sub_one_le_half_exp (-q)).trans (div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2)))

end Erdos3

end

section

namespace Erdos3

theorem exists_quadratic_native_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
        Nonempty (NativeMixedCorrelation 1 N ((p + C) ^ C) f) := by
  obtain ⟨A, _, hbounded⟩ := exists_quadratic_bounded_mixed_correlation
  obtain ⟨B, _, hconvert⟩ := exists_native_mixed_of_bounded 1
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨H, hH, hdense, F, hcorr⟩ := hbounded hp f hf hG
  obtain ⟨W⟩ := hconvert hq f hf H hH hdense F (0, ()) hcorr
  exact ⟨W.mono hbound⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_fixed_mixed_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∀ h ∈ H,
            Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 x, multiplicativeDerivative f h x * star (M.evalCyclic N i (correlationInput h x))‖ := by
  obtain ⟨A, _, hMixed⟩ := exists_quadratic_native_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * Q)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hbound : 2 * q ≤ (p + C) ^ C := by
    simpa [X, Q, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨W⟩ := hMixed hp f hf hG
  obtain ⟨i, H, _, hH, hdense, hcorr⟩ := W.exists_fixed_quadratic_coordinate
  refine ⟨H, hH, ?_, W.mixed.mono hqC, i, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbound))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hbound)).trans (hcorr h hh)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_corner_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ b₁ b₂ b₃ : ZMod N → ℂ,
              (∀ x, ‖b₁ x‖ ≤ 1) ∧ (∀ y, ‖b₂ y‖ ≤ 1) ∧ (∀ z, ‖b₃ z‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 x : ZMod N, 𝔼 y : ZMod N,
                  M.evalCyclic N i (correlationInput y x) *
                    b₁ x * b₂ y * b₃ (x + y)).re := by
  obtain ⟨A, _, hfixed⟩ := exists_quadratic_fixed_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr⟩ := hfixed hp f hf hG
  let g (h n : ZMod N) := M.evalCyclic N i (correlationInput h n)
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hindicator : (𝔼 h : ZMod N, if h ∈ H then Real.exp (-q) else 0) =
      (H.card : ℝ) * Real.exp (-q) / N := by
    rw [Fintype.expect_eq_sum_div_card]
    simp
  have hmean : Real.exp (-(2 * q)) ≤
      𝔼 h : ZMod N, ‖𝔼 n : ZMod N, multiplicativeDerivative f h n * star (g h n)‖ := by
    calc
      _ = Real.exp (-q) * Real.exp (-q) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (H.card : ℝ) * Real.exp (-q) / N := by
        apply (le_div_iff₀ hN).mpr
        nlinarith [mul_le_mul_of_nonneg_right hdense (Real.exp_nonneg (-q))]
      _ = _ := hindicator.symm
      _ ≤ _ := by
        apply Finset.expect_le_expect
        intro h _
        split_ifs with hh
        · exact hcorr h hh
        · exact norm_nonneg _
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hcorner⟩ :=
    exists_correlated_corner f g hf hmean
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, b₁, b₂, b₃, hb₁, hb₂, hb₃, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hcorner

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_exchanged_correlations :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ Q : Finset (ZMod N × ZMod N), Q.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim, ∀ t ∈ Q, Real.exp (-((p + C) ^ C)) ≤
            (𝔼 x : ZMod N, multiplicativeDerivative (multiplicativeDerivative f t.1) t.2 x *
              star (M.evalCyclic N i (correlationInput t.2 x) *
                star (M.evalCyclic N i (correlationInput t.2 (x + t.1))))).re := by
  obtain ⟨A, _, hfixed⟩ := exists_quadratic_fixed_mixed_correlation
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (3 * P + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  classical
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 3 * q + 2 ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, _, hdense, M, i, hcorr⟩ := hfixed hp f hf hG
  let g (h x : ZMod N) := if h ∈ H then M.evalCyclic N i (correlationInput h x) else 0
  have hg (h x : ZMod N) : ‖g h x‖ ≤ 1 := by
    by_cases hh : h ∈ H
    · simp only [g, ite_eq_left hh]
      exact M.norm_eval i _
    · simp only [g, ite_eq_right hh, norm_zero, zero_le_one]
  have hzero (h : ZMod N) (hh : h ∉ H) (x : ZMod N) : g h x = 0 := by
    simp only [g, ite_eq_right hh]
  have hc (h : ZMod N) (hh : h ∈ H) : Real.exp (-q) ≤
      ‖finiteCorrelation Finset.univ (multiplicativeDerivative f h) (g h)‖ := by
    simpa only [g, finiteCorrelation, ite_eq_left hh] using hcorr h hh
  obtain ⟨Q, hQ, hQsize, hQcorr⟩ := exists_many_exchanged_derivative_correlations f g H hf hg hzero
    (Real.exp_pos (-q)) (Real.exp_pos (-q)) (by simpa only [ZMod.card] using hdense) hc
  have hprod : Real.exp (-q) * Real.exp (-q) ^ 2 = Real.exp (-(3 * q)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have hsmall : Real.exp (-((p + C) ^ C)) ≤ Real.exp (-q) * Real.exp (-q) ^ 2 / 2 := by
    rw [hprod]
    exact (Real.exp_le_exp.mpr (by linarith : -((p + C) ^ C) ≤ -(3 * q) - 1)).trans
      (exp_sub_one_le_half_exp (-(3 * q)))
  refine ⟨Q, hQ, ?_, M.mono hqC, i, ?_⟩
  · have hsize : Real.exp (-q) * Real.exp (-q) ^ 2 / 2 * (N : ℝ) ^ 2 ≤ (Q.card : ℝ) := by
      simpa only [ZMod.card] using hQsize
    exact (mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)).trans hsize
  · intro t ht
    obtain ⟨hh, hlarge⟩ := hQcorr t ht
    have hder : multiplicativeDerivative (g t.2) t.1 = fun x =>
        M.evalCyclic N i (correlationInput t.2 x) *
          star (M.evalCyclic N i (correlationInput t.2 (x + t.1))) := by
      funext x
      simp only [multiplicativeDerivative, g, ite_eq_left hh]
    have hlarge' := hsmall.trans hlarge
    rw [hder] at hlarge'
    exact hlarge'

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_reflected_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ (n₀ : ZMod N) (b : ZMod N → ℂ), (∀ y, ‖b y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                (𝔼 y : ZMod N, 𝔼 y' : ZMod N,
                  M.evalCyclic N i (correlationInput y (n₀ - y - y')) *
                    star (M.evalCyclic N i (correlationInput y' (n₀ - y - y'))) *
                    b y * star (b y')).re := by
  obtain ⟨A, _, hcorner⟩ := exists_quadratic_corner_model
  let X : Polynomial ℕ := Polynomial.X
  let P : Polynomial ℕ := (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (2 * P)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have htotal : 2 * q ≤ (p + C) ^ C := by
    simpa [X, P, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, b₁, b₂, b₃, hb₁, hb₂, hb₃, hc⟩ := hcorner hp f hf hG
  obtain ⟨z, b, hb, hreflected⟩ := exists_reflected_corner_correlation
    (fun y x => M.evalCyclic N i (correlationInput y x))
    b₁ b₂ b₃ hb₁ hb₂ hb₃ (Real.exp_nonneg (-q)) hc
  have hpower : Real.exp (-q) ^ 2 = Real.exp (-(2 * q)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [hpower] at hreflected
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, z, b, hb, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg htotal)).trans hreflected

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_quadratic_cyclic_antisymmetric :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p →
      ∀ f : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → Real.exp (-p) ≤ gowersNorm 3 f →
      ∃ H : Finset (ZMod N), H.Nonempty ∧
        Real.exp (-((p + C) ^ C)) * N ≤ (H.card : ℝ) ∧
        ∃ M : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) ((p + C) ^ C),
          ∃ i : Fin M.outputDim,
            (∀ h ∈ H, Real.exp (-((p + C) ^ C)) ≤
              ‖𝔼 n : ZMod N, multiplicativeDerivative f h n *
                star (M.evalCyclic N i (correlationInput h n))‖) ∧
            ∃ (i' j' : Fin M.outputDim) (a b : ZMod N → ℂ),
              (∀ x, ‖a x‖ ≤ 1) ∧ (∀ y, ‖b y‖ ≤ 1) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
                  star (M.evalCyclic N i' (correlationInput x y)) *
                    M.evalCyclic N j' (correlationInput y x) * a x * b y‖ := by
  obtain ⟨A, _, hreflect⟩ := exists_quadratic_reflected_model
  obtain ⟨B, _, hanti⟩ := exists_integer_antisymmetric_correlation
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A
  let R := 2 * Q + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro N _ p hp f hf hG
  let q := (p + A) ^ A
  let r := 2 * q + 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hcost : r + (r + B) ^ B ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  have hr : 0 ≤ r := hq.trans hqr
  have hqC : q ≤ (p + C) ^ C := by have := pow_nonneg (by positivity : 0 ≤ r + B) B; linarith
  have hfinal : (r + B) ^ B ≤ (p + C) ^ C := by linarith
  obtain ⟨H, hH, hdense, M, i, hcorr, z, b, hb, hreflected⟩ := hreflect hp f hf hG
  have heval (k : Fin M.outputDim) (x n : ZMod N) :
      M.eval k (correlationInput (x.val : ℤ) (n.val : ℤ)) = M.evalCyclic N k (correlationInput x n) := by
    apply congrArg (M.eval k)
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  let F (x n : ℤ) := M.eval i (correlationInput x n)
  have hc : Real.exp (-q) ≤ ‖𝔼 x : ZMod N, 𝔼 y : ZMod N,
      F x.val (z - x - y).val * star (F y.val (z - x - y).val) * b x * star (b y)‖ := by
    simpa only [F, heval] using hreflected.trans (Complex.re_le_norm _)
  obtain ⟨k, a₀, b₀, ha₀, hb₀, hunwrapped⟩ := exists_unwrapped_reflected_correlation
    hq F F (fun _ _ => M.norm_eval i _) (fun _ _ => M.norm_eval i _) z b hb hc
  have hpairMean (g : ZMod N → ZMod N → ℂ) :
      (𝔼 u : ZMod N × ZMod N, g u.1 u.2) = 𝔼 x : ZMod N, 𝔼 y : ZMod N, g x y := by
    rw [← Finset.univ_product_univ, Finset.expect_product]
  obtain ⟨i', j', a₁, b₁, ha₁, hb₁, hantisymmetric⟩ := hanti (M.mono hqr)
    ((z.val : ℤ) + (k.val : ℤ) * N) i i (Finset.univ : Finset (ZMod N × ZMod N))
    Finset.univ_nonempty (fun u => (u.1.val : ℤ)) (fun u => (u.2.val : ℤ))
    a₀ b₀ ha₀ hb₀ (by
      simpa only [← Finset.univ_product_univ, Finset.expect_product,
        NativeMultidegreeNilcharacter.mono_eval, r, F] using hunwrapped)
  change Fin M.outputDim at i' j'
  change Real.exp (-((r + B) ^ B)) ≤
    ‖𝔼 u : ZMod N × ZMod N,
      star (M.eval i' (correlationInput (u.1.val : ℤ) (u.2.val : ℤ))) *
        M.eval j' (correlationInput (u.2.val : ℤ) (u.1.val : ℤ)) *
        a₁ u.1.val * b₁ u.2.val‖ at hantisymmetric
  rw [hpairMean (fun x y =>
    star (M.eval i' (correlationInput (x.val : ℤ) (y.val : ℤ))) *
      M.eval j' (correlationInput (y.val : ℤ) (x.val : ℤ)) *
      a₁ x.val * b₁ y.val)] at hantisymmetric
  simp_rw [heval] at hantisymmetric
  refine ⟨H, hH, ?_, M.mono hqC, i, ?_, i', j', (fun x => a₁ x.val), (fun y => b₁ y.val),
    (fun x => ha₁ _), (fun y => hb₁ _), ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh)
  · exact (Real.exp_le_exp.mpr (neg_le_neg hfinal)).trans hantisymmetric

end Erdos3

end

end OAI
