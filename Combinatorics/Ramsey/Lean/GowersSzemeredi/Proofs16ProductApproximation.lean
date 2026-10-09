import GowersSzemeredi.Proofs16UniformTruncation
import GowersSzemeredi.Proofs16BohrLargeSpectrumSpan

/-! Control the product of truncated trapezoids and discharge the
approximation hypothesis in the bounded-span bridge. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Uniform errors for factors of norm at most one give an explicit
product error; the empty product case is included. -/
theorem norm_product_approximation {ι : Type*} (s : Finset ι) (f g : ι → Complex)
    {eta : Real} (heta : 0 ≤ eta) (hf : ∀ i ∈ s, ‖f i‖ ≤ 1)
    (hfg : ∀ i ∈ s, ‖f i - g i‖ ≤ eta) :
    ‖(∏ i ∈ s, f i) - ∏ i ∈ s, g i‖ ≤ (1 + eta)^s.card - 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hdiff := hfg i (Finset.mem_insert_self _ _)
    have hfs : ∀ j ∈ s, ‖f j‖ ≤ 1 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    have hfgs : ∀ j ∈ s, ‖f j - g j‖ ≤ eta := fun j hj => hfg j (Finset.mem_insert_of_mem hj)
    have hgi : ‖g i‖ ≤ 1 + eta := by
      have ht := norm_add_le (f i) (g i - f i)
      rw [add_sub_cancel, norm_sub_rev] at ht
      linarith
    have hprod : ‖∏ j ∈ s, f j‖ ≤ 1 := by
      exact (Finset.norm_prod_le _ _).trans (Finset.prod_le_one (fun j _ => norm_nonneg _) hfs)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.card_insert_of_notMem hi]
    have heq : f i * (∏ j ∈ s, f j) - g i * (∏ j ∈ s, g j) =
        g i * ((∏ j ∈ s, f j) - ∏ j ∈ s, g j) + (f i - g i) * (∏ j ∈ s, f j) := by ring
    rw [heq]
    calc
      _ ≤ ‖g i‖ * ‖(∏ j ∈ s, f j) - ∏ j ∈ s, g j‖ +
          ‖f i - g i‖ * ‖∏ j ∈ s, f j‖ := by rw [← norm_mul, ← norm_mul]; exact norm_add_le _ _
      _ ≤ (1 + eta) * ((1 + eta)^s.card - 1) + eta * 1 :=
        add_le_add (mul_le_mul hgi (ih hfs hfgs) (norm_nonneg _) (by linarith))
          (mul_le_mul hdiff hprod (norm_nonneg _) heta)
      _ = (1 + eta)^(s.card + 1) - 1 := by rw [pow_succ]; ring

/-- The product of truncated Fourier expansions approximates the product
of trapezoids with a fully explicit error. -/
theorem trapezoid_product_uniform_truncation {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) {a c : Nat} (ha : 2 * a < N) (hc : 2 * c < N)
    (R : Nat) (x : ZMod N) :
    ‖((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex) -
      boundedCharacterProduct (fun gamma : K => (gamma : ZMod N)) R
        (fun _ r => (N : Complex)⁻¹ *
          fourier (fun t => ((trapezoid a c t : Real) : Complex)) (r : ZMod N)) x‖ ≤
      (1 + N / ((centeredBall N c).card * (R + 1 : Real)))^K.card - 1 := by
  have heq : boundedCharacterProduct (fun gamma : K => (gamma : ZMod N)) R
      (fun _ r => (N : Complex)⁻¹ *
        fourier (fun t => ((trapezoid a c t : Real) : Complex)) (r : ZMod N)) x =
      ∏ gamma ∈ K, centeredFourierTruncation
        (fun t => ((trapezoid a c t : Real) : Complex)) R (gamma * x) := by
    unfold boundedCharacterProduct centeredFourierTruncation
    conv_rhs => rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro gamma _
    rw [Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro r _
    simp only [mul_assoc]
  rw [heq, Complex.ofReal_prod]
  apply norm_product_approximation
  · positivity
  · intro gamma hgamma
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (trapezoid_nonneg _ _ _)]
    exact trapezoid_le_one _ _ _
  · intro gamma hgamma
    exact trapezoid_uniform_truncation ha hc R (gamma * x)

/-- Large Bohr Fourier coefficients lie in a bounded frequency span
under a purely numerical error budget; no approximation hypothesis remains. -/
theorem large_bohr_fourier_mem_boundedSpan_of_budget {N : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) {a c : Nat} (hca : c ≤ a)
    (ha : 2 * a < N) (hc : 2 * c < N) (R : Nat) {epsilon : Real}
    (hbudget : K.card * (4 * (c : Real) + 2) +
      ((1 + N / ((centeredBall N c).card * (R + 1 : Real)))^K.card - 1) * N < epsilon * N)
    {xi : ZMod N} (hlarge : epsilon * N ≤ ‖fourier (indicator (bohr K ((a : Real) / N))) xi‖) :
    xi ∈ boundedFrequencySpan (fun gamma : K => (gamma : ZMod N)) R := by
  exact large_bohr_fourier_mem_boundedFrequencySpan K a c R hca _
    (trapezoid_product_uniform_truncation K ha hc R) hbudget hlarge

end LeanProofs.GowersSzemeredi
