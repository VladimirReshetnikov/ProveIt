import OAI.Combinatorics.Progressions.Fourier.FiniteFourierSmoothing

namespace OAI

section

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

theorem IsWeightedDissociated.mono_K {mu : G → ℝ} {K L : ℝ}
    {Delta : Finset (AddChar G ℂ)}
    (h : IsWeightedDissociated mu K Delta) (hKL : K ≤ L) :
    IsWeightedDissociated mu L Delta := by
  intro u hu
  exact (h u hu).trans (Real.exp_le_exp.mpr hKL)

theorem IsWeightedDissociated.mono_subset {mu : G → ℝ} {K : ℝ}
    {Delta Gamma : Finset (AddChar G ℂ)}
    (h : IsWeightedDissociated mu K Delta) (hsub : Gamma ⊆ Delta) :
    IsWeightedDissociated mu K Gamma := by
  intro u hu
  let v : AddChar G ℂ → ℂ := fun psi ↦ if psi ∈ Gamma then u psi else 0
  have hv : ∀ psi ∈ Delta, ‖v psi‖ ≤ 1 := by
    intro psi hpsi
    by_cases hp : psi ∈ Gamma
    · simpa [v, hp] using hu psi hp
    · simp [v, hp]
  have heq (x : G) :
      ∏ psi ∈ Delta, (1 + (v psi * psi x).re) =
        ∏ psi ∈ Gamma, (1 + (u psi * psi x).re) := by
    rw [← Finset.prod_subset hsub]
    · apply prod_congr rfl
      intro psi hpsi
      simp [v, hpsi]
    · intro psi hpsiDelta hpsiGamma
      simp [v, hpsiGamma]
  simpa only [heq] using h v hv

omit [AddCommGroup G] in

theorem exp_weightedAverage_le_weightedAverage_exp
    (w : G → ℝ) (hw : ∀ x, 0 ≤ w x) (hw_sum : ∑ x : G, w x = 1)
    (f : G → ℝ) :
    exp (∑ x : G, w x * f x) ≤ ∑ x : G, w x * exp (f x) := by
  have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset G))
    (p := f) (fun x _ ↦ hw x) (by simpa using hw_sum)
    (fun x _ ↦ Set.mem_univ (f x))
  simpa using h

theorem weighted_rudin_exp_ineq
    (mu : G → ℝ) (K : ℝ) (Delta : Finset (AddChar G ℂ))
    (hmu : ∀ x, 0 ≤ mu x)
    (hDelta : IsWeightedDissociated mu K Delta)
    (c : AddChar G ℂ → ℂ) :
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
      exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
  have hexp (z : ℂ) :
      exp z.re ≤ cosh ‖z‖ + (z / ‖z‖).re * sinh ‖z‖ := by
    calc
      _ = exp ((z / ‖z‖).re * ‖z‖) := by
        obtain rfl | hz := eq_or_ne z 0 <;> simp [*]
      _ ≤ _ := exp_mul_le_cosh_add_mul_sinh
        (by simpa using z.abs_re_div_norm_le_one) _
  choose u hu huc using fun psi ↦ Complex.exists_norm_mul_eq_self (c psi)
  have hu0 (psi : AddChar G ℂ) : u psi ≠ 0 := fun h ↦ by
    simpa [h] using hu psi
  have hpoint (x : G) :
      exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
    calc
      exp ((∑ psi ∈ Delta, c psi * psi x).re) =
          ∏ psi ∈ Delta, exp ((c psi * psi x).re) := by
            simp_rw [← exp_sum, ← Complex.re_sum]
      _ ≤ ∏ psi ∈ Delta,
          (cosh ‖c psi * psi x‖ +
            ((c psi * psi x) / ‖c psi * psi x‖).re *
              sinh ‖c psi * psi x‖) := by
        gcongr with psi hpsi
        exact hexp _
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ +
            (u psi * (c psi * psi x) / (u psi * ↑‖c psi‖)).re *
              sinh ‖c psi‖) := by
        apply prod_congr rfl
        intro psi hpsi
        rw [norm_mul, AddChar.norm_apply, mul_one,
          mul_div_mul_left _ _ (hu0 psi)]
      _ = ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
        apply prod_congr rfl
        intro psi hpsi
        obtain hc | hc := eq_or_ne (c psi) 0
        · simp [hc]
        simp only [huc, mul_left_comm (u psi), mul_div_cancel_left₀ _ hc,
          ← Complex.re_mul_ofReal, mul_right_comm]
  let q : AddChar G ℂ → ℝ := fun psi ↦ sinh ‖c psi‖ / cosh ‖c psi‖
  let v : AddChar G ℂ → ℂ := fun psi ↦ (q psi : ℂ) * u psi
  have hfactor (x : G) :
      (∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re)) =
        (∏ psi ∈ Delta, cosh ‖c psi‖) *
          (∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
    rw [← Finset.prod_mul_distrib]
    apply prod_congr rfl
    intro psi hpsi
    have hcosh : cosh ‖c psi‖ ≠ 0 := ne_of_gt (cosh_pos _)
    have hsinh_re :
        (u psi * (sinh ‖c psi‖ : ℂ) * psi x).re =
          sinh ‖c psi‖ * (u psi * psi x).re := by
      rw [show u psi * (sinh ‖c psi‖ : ℂ) * psi x =
          (sinh ‖c psi‖ : ℂ) * (u psi * psi x) by ring]
      exact Complex.re_ofReal_mul _ _
    have hv_re : (v psi * psi x).re = q psi * (u psi * psi x).re := by
      rw [show v psi * psi x = (q psi : ℂ) * (u psi * psi x) by
        simp [v]; ring]
      exact Complex.re_ofReal_mul _ _
    rw [hsinh_re, hv_re]
    dsimp [q]
    field_simp
  calc
    ∑ x : G, mu x * exp ((∑ psi ∈ Delta, c psi * psi x).re) ≤
        ∑ x : G, mu x * ∏ psi ∈ Delta,
          (cosh ‖c psi‖ + (u psi * sinh ‖c psi‖ * psi x).re) := by
      apply sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (hpoint x) (hmu x)
    _ = (∏ psi ∈ Delta, cosh ‖c psi‖) *
        (∑ x : G, mu x *
          ∏ psi ∈ Delta,
            (1 + (v psi * psi x).re)) := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro x hx
      rw [hfactor]
      ring
    _ ≤ (∏ psi ∈ Delta, cosh ‖c psi‖) * exp K := by
      gcongr
      apply hDelta v
      intro psi hpsi
      have hq : |q psi| ≤ 1 := by
        simpa [q, Real.tanh_eq_sinh_div_cosh] using (Real.abs_tanh_lt_one ‖c psi‖).le
      simpa [v, norm_mul, hu psi, Complex.norm_real, Real.norm_eq_abs] using hq
    _ ≤ exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) * exp K := by
      apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
      calc
        ∏ psi ∈ Delta, cosh ‖c psi‖ ≤
            ∏ psi ∈ Delta, exp (‖c psi‖ ^ 2 / 2) := by
          gcongr with psi hpsi
          exact cosh_le_exp_half_sq _
        _ = exp ((∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
          simp_rw [← exp_sum, ← sum_div]
    _ = exp (K + (∑ psi ∈ Delta, ‖c psi‖ ^ 2) / 2) := by
      rw [← exp_add]
      congr 1
      ring

end Erdos3.RelativeChangSanders

end

end

end OAI
