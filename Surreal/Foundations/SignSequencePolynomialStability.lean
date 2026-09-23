import Surreal.Foundations.SignSequenceRootNormalization
import Surreal.Foundations.SignSequenceValuationBounds

/-!
# A valuation-controlled simple polynomial root

The scalar polynomial normalization behind `trigonometry:thm:stability`
works with actual surreal valuation exponents of arbitrary rank. If the
constant error and linear-coefficient error have valuation at least `σ`,
`v(A)=κ≥0`, `σ>2κ`, and higher coefficients are finite, there is a unique
simple root in the closed ball `v(h)≥σ-κ`. A second normalization proves
uniqueness on the larger neighborhood `v(h)>κ`. Applying this polynomial
result to the exact trigonometric chart remains a separate step.
-/

universe u

namespace Surreal.Foundations.SignSequence

open Polynomial

noncomputable section

/-- Finiteness after dividing by any element with a specified finite valuation. -/
theorem isFinite_div_iff_of_valuation (x a k : SignSequence.{u}) (ha : valuation a = ↑k) :
    IsFinite (x / a) ↔ (k : WithTop SignSequence.{u}) ≤ valuation x := by
  rw [isFinite_iff_valuation_nonneg, valuation_div, ha]
  cases hx : valuation x with
  | top => simp
  | coe b =>
    change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) ≤ ↑(b - k) ↔ ↑k ≤ (b : WithTop SignSequence.{u})
    simp only [WithTop.coe_le_coe, sub_nonneg]

/-- Infinitesimality after the same division is the strict valuation comparison. -/
theorem isInfinitesimal_div_iff_of_valuation (x a k : SignSequence.{u}) (ha : valuation a = ↑k) :
    IsInfinitesimal (x / a) ↔ (k : WithTop SignSequence.{u}) < valuation x := by
  rw [isInfinitesimal_iff_valuation_pos, valuation_div, ha]
  cases hx : valuation x with
  | top => simp
  | coe b =>
    change ((0 : SignSequence.{u}) : WithTop SignSequence.{u}) < ↑(b - k) ↔ ↑k < (b : WithTop SignSequence.{u})
    simp only [WithTop.coe_lt_coe, sub_pos]

/-- A polynomial with the stated error valuations has a unique simple root at the predicted scale. -/
theorem exists_unique_polynomial_root_of_error_valuation
    (P : Polynomial SignSequence.{u}) (A k s : SignSequence.{u})
    (hA : valuation A = ↑k) (hk : 0 ≤ k) (hs : 2 * k < s)
    (h0 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 0))
    (h1 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 1 - A))
    (hh : ∀ n, IsFinite (P.coeff (n + 2))) :
    ∃ h : SignSequence.{u}, (s - k : SignSequence.{u}) ≤ valuation h ∧
      P.IsRoot h ∧ P.rootMultiplicity h = 1 ∧
        ∀ y, (s - k : SignSequence.{u}) ≤ valuation y → P.IsRoot y → y = h := by
  have hA0 : A ≠ 0 := by
    intro he
    rw [he, valuation_zero] at hA
    exact WithTop.top_ne_coe hA
  have hsk : k < s := by linarith
  have hrk : k < s - k := by linarith
  have hr : 0 ≤ s - k := le_trans hk hrk.le
  let l := tMonomial (s - k)
  have hl : l ≠ 0 := tMonomial_ne_zero _
  have hlf : IsFinite l := by
    rw [isFinite_iff_valuation_nonneg, valuation_tMonomial]
    exact_mod_cast hr
  have hla : IsInfinitesimal (l / A) := by
    rw [isInfinitesimal_div_iff_of_valuation l A k hA, valuation_tMonomial]
    exact_mod_cast hrk
  have hAl : valuation (A * l) = (s : WithTop SignSequence.{u}) := by
    rw [valuation_mul, hA, valuation_tMonomial, ← WithTop.coe_add, add_sub_cancel]
  have hc0 : IsFinite (P.coeff 0 / (A * l)) :=
    (isFinite_div_iff_of_valuation _ _ _ hAl).mpr h0
  have hc1 : IsInfinitesimal (P.coeff 1 / A - 1) := by
    have he : P.coeff 1 / A - 1 = (P.coeff 1 - A) / A := by field_simp
    rw [he, isInfinitesimal_div_iff_of_valuation _ _ _ hA]
    exact (show (k : WithTop SignSequence.{u}) < s by exact_mod_cast hsk).trans_le h1
  obtain ⟨h, hhf, hroot, hmult, hu⟩ :=
    exists_unique_root_at_scale P A l hl hlf hla hc0 hc1 hh hA0
  refine ⟨h, (isFinite_div_tMonomial_iff h (s - k)).mp hhf, hroot, hmult, ?_⟩
  intro y hy hyr
  exact hu y ((isFinite_div_tMonomial_iff y (s - k)).mpr hy) hyr

/-- The same root is unique on the larger open neighborhood appearing in the source. -/
theorem exists_unique_polynomial_root_in_open_neighborhood
    (P : Polynomial SignSequence.{u}) (A k s : SignSequence.{u})
    (hA : valuation A = ↑k) (hk : 0 ≤ k) (hs : 2 * k < s)
    (h0 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 0))
    (h1 : (s : WithTop SignSequence.{u}) ≤ valuation (P.coeff 1 - A))
    (hh : ∀ n, IsFinite (P.coeff (n + 2))) :
    ∃ h : SignSequence.{u}, (k : WithTop SignSequence.{u}) < valuation h ∧
      (s - k : SignSequence.{u}) ≤ valuation h ∧ P.IsRoot h ∧ P.rootMultiplicity h = 1 ∧
        ∀ y, (k : WithTop SignSequence.{u}) < valuation y → P.IsRoot y → y = h := by
  have hA0 : A ≠ 0 := by
    intro he
    rw [he, valuation_zero] at hA
    exact WithTop.top_ne_coe hA
  have hsk : k < s := by linarith
  have hrk : k < s - k := by linarith
  let l := tMonomial k
  have hl : l ≠ 0 := tMonomial_ne_zero _
  have hlf : IsFinite l := by
    rw [isFinite_iff_valuation_nonneg, valuation_tMonomial]
    exact_mod_cast hk
  have hla : IsFinite (l / A) := by
    rw [isFinite_div_iff_of_valuation l A k hA, valuation_tMonomial]
  have hAl : valuation (A * l) = ((2 * k : SignSequence.{u}) : WithTop SignSequence.{u}) := by
    rw [valuation_mul, hA, valuation_tMonomial, ← WithTop.coe_add, ← two_mul]
  have hc0 : IsInfinitesimal (P.coeff 0 / (A * l)) := by
    rw [isInfinitesimal_div_iff_of_valuation _ _ _ hAl]
    exact (show ((2 * k : SignSequence.{u}) : WithTop SignSequence.{u}) < s by
      exact_mod_cast hs).trans_le h0
  have hc1 : IsInfinitesimal (P.coeff 1 / A - 1) := by
    have he : P.coeff 1 / A - 1 = (P.coeff 1 - A) / A := by field_simp
    rw [he, isInfinitesimal_div_iff_of_valuation _ _ _ hA]
    exact (show (k : WithTop SignSequence.{u}) < s by exact_mod_cast hsk).trans_le h1
  let N := FinitePolynomial.rootNormalization P A l
  have hN := rootNormalization_finite_of_finite_ratio P A l hl hlf hla
    (finite_of_infinitesimal hc0) (finite_of_infinitesimal_sub_one hc1) hh
  have hred0 : (reducePolynomial N hN).coeff 0 = 0 := by
    rw [reducePolynomial_coeff, FinitePolynomial.rootNormalization_coeff_zero]
    exact (standardPart_eq_zero_iff (finite_of_infinitesimal hc0)).mpr hc0
  have hred1 : (reducePolynomial N hN).coeff 1 = 1 := by
    rw [reducePolynomial_coeff, FinitePolynomial.rootNormalization_coeff_one P A l hl]
    exact standardPart_eq_one_of_infinitesimal_sub_one hc1
  have hc : (reducePolynomial N hN).IsRoot 0 := by
    simpa only [IsRoot.def, ← coeff_zero_eq_eval_zero] using hred0
  have hd : (reducePolynomial N hN).derivative.eval 0 ≠ 0 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative]
    simp [hred1]
  obtain ⟨z, _, hu⟩ := existsUnique_finite_root_of_simple_reduction N hN 0 hc hd
  have hcand (y : SignSequence.{u}) (hy : (k : WithTop SignSequence.{u}) < valuation y)
      (hyr : P.IsRoot y) : IsFinite (y / l) ∧ N.IsRoot (y / l) ∧ standardPart (y / l) = 0 := by
    have hi := (isInfinitesimal_div_tMonomial_iff y k).mpr hy
    refine ⟨finite_of_infinitesimal hi, ?_,
      (standardPart_eq_zero_iff (finite_of_infinitesimal hi)).mpr hi⟩
    exact (FinitePolynomial.isRoot_rootNormalization_iff P A l (y / l) hA0 hl).mpr
      (by simpa only [mul_div_cancel₀ y hl] using hyr)
  obtain ⟨h, hv, hroot, hm, _⟩ :=
    exists_unique_polynomial_root_of_error_valuation P A k s hA hk hs h0 h1 hh
  have hv' : (k : WithTop SignSequence.{u}) < valuation h :=
    (show (k : WithTop SignSequence.{u}) < (s - k : SignSequence.{u}) by
      exact_mod_cast hrk).trans_le hv
  refine ⟨h, hv', hv, hroot, hm, ?_⟩
  intro y hy hyr
  have he := (hu (y / l) (hcand y hy hyr)).trans (hu (h / l) (hcand h hv' hroot)).symm
  have he' := congrArg (fun q => q * l) he
  simpa only [div_mul_cancel₀ _ hl] using he'

end
end Surreal.Foundations.SignSequence
