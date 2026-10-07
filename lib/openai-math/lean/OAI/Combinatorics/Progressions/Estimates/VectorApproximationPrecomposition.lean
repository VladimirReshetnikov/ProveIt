import OAI.Combinatorics.Progressions.Linear.FiniteNormalizedFrame

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem vector_approximation_precision {I : Type*} [Fintype I] {q epsilon : ℝ}
    (a : ℕ) (hq : 0 ≤ q) (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (hepsilon : 0 < epsilon) (hscale : 1 / epsilon ≤ Real.exp ((q + 2) ^ a)) :
    0 < epsilon / (Fintype.card I + 1 : ℝ) ∧
      1 / (epsilon / (Fintype.card I + 1 : ℝ)) ≤ Real.exp ((q + 2) ^ (a + 1)) := by
  have hcard : (0 : ℝ) < Fintype.card I + 1 := by positivity
  refine ⟨div_pos hepsilon hcard, ?_⟩
  have hcount : (Fintype.card I + 1 : ℝ) ≤ Real.exp (q + 1) := by
    rw [Real.exp_add]
    nlinarith [Real.one_le_exp hq, Real.add_one_le_exp (1 : ℝ)]
  have hpow : 1 ≤ (q + 2) ^ a := one_le_pow₀ (by linarith)
  have hexponent : q + 1 + (q + 2) ^ a ≤ (q + 2) ^ (a + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ = (Fintype.card I + 1 : ℝ) * (1 / epsilon) := by field_simp
    _ ≤ Real.exp (q + 1) * Real.exp ((q + 2) ^ a) :=
      mul_le_mul hcount hscale (by positivity) (Real.exp_nonneg _)
    _ = Real.exp (q + 1 + (q + 2) ^ a) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hexponent

theorem euclidean_coefficient_norm_le_exp {I : Type*} [Fintype I] {q : ℝ}
    (hq : 0 ≤ q) (hI : (Fintype.card I : ℝ) ≤ Real.exp q)
    (c : EuclideanSpace ℂ I) (hc : ∀ i, ‖c i‖ ≤ 2) :
    ‖c‖ ≤ Real.exp (q + 2) := by
  have h := euclidean_norm_le_card_add_one_mul c (by norm_num : (0 : ℝ) ≤ 2) hc
  have hfour : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  rw [Real.exp_add]
  nlinarith [Real.one_le_exp hq,
    mul_le_mul_of_nonneg_left hfour (Real.exp_nonneg q)]

theorem euclidean_error_le_of_coordinate_errors {I : Type*} [Fintype I]
    (v : EuclideanSpace ℂ I) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hv : ∀ i, ‖v i‖ ≤ epsilon / (Fintype.card I + 1 : ℝ)) :
    ‖v‖ ≤ epsilon := by
  have h := euclidean_norm_le_card_add_one_mul v (div_nonneg hepsilon (by positivity)) hv
  have hcard : (Fintype.card I + 1 : ℝ) ≠ 0 := by positivity
  simpa only [mul_div_cancel₀ _ hcard] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem scalar_error_le_of_vector_error {I J S : Type*} [Fintype I] [Fintype J]
    (u : I → S → ℂ) (w : J → S → ℂ) (c : J → EuclideanSpace ℂ I)
    {epsilon : ℝ}
    (herror : ∀ x, ‖(WithLp.toLp 2 (fun k => u k x) : EuclideanSpace ℂ I) -
      ∑ j, w j x • c j‖ ≤ epsilon) (k : I) :
    ∀ x, ‖u k x - ∑ j, w j x * c j k‖ ≤ epsilon := by
  intro x
  have h := (PiLp.norm_apply_le
    ((WithLp.toLp 2 (fun k => u k x) : EuclideanSpace ℂ I) - ∑ j, w j x • c j) k).trans (herror x)
  simpa only [PiLp.sub_apply, PiLp.toLp_apply, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] using h

theorem norm_complex_half_le_one {c : ℂ} (hc : ‖c‖ ≤ 2) : ‖c / 2‖ ≤ 1 := by
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  rw [norm_div, htwo]
  linarith only [hc]

theorem sum_double_half_products {J : Type*} [Fintype J] (a b c : J → ℂ) :
    (∑ j : Bool × J, (c j.2 / 2 * a j.2) * b j.2) = ∑ j, (a j * b j) * c j := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem vector_approximation_precompose {I J S X : Type*} [Fintype I] [Fintype J]
    [PseudoMetricSpace X] (f : X → X) (y z : S → X) (w : J → S → ℂ)
    {A : ℝ≥0} (hf : LipschitzWith A f) (heval : ∀ x, f (y x) = z x)
    {p q B B' epsilon : ℝ} (hscale : Real.exp p * (A : ℝ) ≤ Real.exp q) (hB : B ≤ B')
    (happrox : ∀ (u : I → X → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp q →
      (∀ k, LipschitzWith ell (u k)) → (∀ k x, ‖u k x‖ ≤ 1) →
      ∃ c : J → EuclideanSpace ℂ I, (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ B) ∧
        ∀ x, ‖(WithLp.toLp 2 (fun k => u k (y x)) : EuclideanSpace ℂ I) -
          ∑ j, w j x • c j‖ ≤ epsilon) :
    ∀ (u : I → X → ℂ) (ell : ℝ≥0), (ell : ℝ) ≤ Real.exp p →
      (∀ k, LipschitzWith ell (u k)) → (∀ k x, ‖u k x‖ ≤ 1) →
      ∃ c : J → EuclideanSpace ℂ I, (∀ j k, ‖c j k‖ ≤ 2) ∧ (∀ j, ‖c j‖ ≤ B') ∧
        ∀ x, ‖(WithLp.toLp 2 (fun k => u k (z x)) : EuclideanSpace ℂ I) -
          ∑ j, w j x • c j‖ ≤ epsilon := by
  intro u ell hell hu hub
  have hbound : ((ell * A : ℝ≥0) : ℝ) ≤ Real.exp q :=
    (mul_le_mul_of_nonneg_right hell A.coe_nonneg).trans hscale
  obtain ⟨c, hc, hcB, herr⟩ := happrox (fun k x => u k (f x)) (ell * A) hbound
    (fun k => (hu k).comp hf) (fun k x => hub k (f x))
  refine ⟨c, hc, fun j => (hcB j).trans hB, ?_⟩
  intro x
  simpa only [heval x] using herr x

end Erdos3

end

end OAI
