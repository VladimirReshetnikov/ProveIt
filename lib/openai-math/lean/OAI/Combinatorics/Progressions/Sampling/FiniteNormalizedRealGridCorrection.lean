/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Data.Real.Basic
import OAI.Combinatorics.Progressions.Geometry.FiniteNormalizedChartCorrection

namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem exists_finiteSupport_rationalGridLift {V : Type*}
    (S : Finset (V →₀ ℕ)) (P : MvPolynomial V ℝ) (q : ℕ)
    (hsupport : P.support ⊆ S)
    (hgrid : ∀ α : V →₀ ℕ, ∃ z : ℤ, P.coeff α = (z : ℝ) / (q : ℝ)) :
    ∃ r : MvPolynomial V ℚ, r.support ⊆ S ∧
      (∀ α : V →₀ ℕ, ∃ z : ℤ, r.coeff α = (z : ℚ) / (q : ℚ)) ∧
      MvPolynomial.map (Rat.castHom ℝ) r = P := by
  classical
  let z : S → ℤ := fun α => Classical.choose (hgrid α.val)
  let c : S → ℚ := fun α => (z α : ℚ) / (q : ℚ)
  let r := polynomialOfFiniteCoefficientVector S c
  have hcoeff (α : S) : r.coeff α.val = c α :=
    polynomialOfFiniteCoefficientVector_coeff S c α
  have hzero (α : V →₀ ℕ) (hα : α ∉ S) : r.coeff α = 0 :=
    polynomialOfFiniteCoefficientVector_coeff_eq_zero_of_not_mem S c α hα
  refine ⟨r, polynomialOfFiniteCoefficientVector_support_subset S c, ?_, ?_⟩
  · intro α
    by_cases hα : α ∈ S
    · exact ⟨z ⟨α, hα⟩, hcoeff ⟨α, hα⟩⟩
    · refine ⟨0, ?_⟩
      rw [hzero α hα]
      simp only [Int.cast_zero, zero_div]
  · ext α
    rw [MvPolynomial.coeff_map]
    by_cases hα : α ∈ S
    · rw [hcoeff ⟨α, hα⟩]
      change (Rat.castHom ℝ) ((z ⟨α, hα⟩ : ℚ) / (q : ℚ)) = P.coeff α
      simp only [map_div₀, map_intCast, map_natCast]
      exact (Classical.choose_spec (hgrid α)).symm
    · rw [hzero α hα, map_zero]
      exact (MvPolynomial.notMem_support_iff.mp (fun h => hα (hsupport h))).symm

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {U V : Type*}

def normalizedRealGridCorrectionSolutions
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ) :
    Set (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℝ) :=
  {sr | sr.1.support ⊆ S ∧ sr.2.support ⊆ S ∧
    (∀ α, |sr.1.coeff α| ≤ B) ∧
    (∀ α, ∃ z : ℤ, sr.2.coeff α = (z : ℝ) / q) ∧
    P = aeval (R := ℝ) (normalizedRealPolynomialChart H A) sr.1 + sr.2}

private theorem normalizedChartCorrectionSolutions_map
    (H : U → ℝ) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ) (B : ℝ) (q : ℕ)
    (sr : MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℚ)
    (hsr : sr ∈ normalizedChartCorrectionSolutions H A S P B q) :
    (sr.1, MvPolynomial.map (Rat.castHom ℝ) sr.2) ∈
      normalizedRealGridCorrectionSolutions H A S P B q := by
  refine ⟨hsr.1, (support_map_subset (Rat.castHom ℝ) sr.2).trans hsr.2.1,
    hsr.2.2.1, ?_, hsr.2.2.2.2⟩
  intro α
  obtain ⟨z, hz⟩ := hsr.2.2.2.1 α
  refine ⟨z, ?_⟩
  rw [coeff_map, hz]
  simp

theorem exists_finite_normalized_real_grid_corrections
    (H : U → ℝ) (hH : ∀ i, 1 ≤ H i) (A : V → MvPolynomial U ℝ)
    (S : Finset ((U ⊕ V) →₀ ℕ)) (P : MvPolynomial (U ⊕ V) ℝ)
    (B : ℝ) (hB : 0 ≤ B) (q : ℕ) (hq : 0 < q) :
    ∃ m : ℕ, m ≤ (2 * ⌈(q : ℝ) * B⌉₊ + 3) ^ S.card ∧
      ∃ candidate : Fin m → (MvPolynomial (U ⊕ V) ℝ × MvPolynomial (U ⊕ V) ℝ),
        (∀ j, candidate j ∈ normalizedRealGridCorrectionSolutions H A S P B q) ∧
        ∀ sr, sr ∈ normalizedRealGridCorrectionSolutions H A S P B q →
          ∃ j, candidate j = sr := by
  obtain ⟨m, hm, candidate, hvalid, hcomplete⟩ :=
    exists_finite_normalized_chart_corrections H hH A S P B hB q hq
  refine ⟨m, hm, (fun j => ((candidate j).1,
    MvPolynomial.map (Rat.castHom ℝ) (candidate j).2)), ?_, ?_⟩
  · intro j
    exact normalizedChartCorrectionSolutions_map H A S P B q (candidate j) (hvalid j)
  · intro sr hsr
    obtain ⟨r, hrsupport, hrgrid, hrmap⟩ :=
      exists_finiteSupport_rationalGridLift S sr.2 q hsr.2.1 hsr.2.2.2.1
    have hr : (sr.1, r) ∈ normalizedChartCorrectionSolutions H A S P B q := by
      refine ⟨hsr.1, hrsupport, hsr.2.2.1, hrgrid, ?_⟩
      rw [hrmap]
      exact hsr.2.2.2.2
    obtain ⟨j, hj⟩ := hcomplete (sr.1, r) hr
    refine ⟨j, ?_⟩
    change ((candidate j).1, MvPolynomial.map (Rat.castHom ℝ) (candidate j).2) = sr
    rw [hj]
    exact Prod.ext rfl hrmap

end Erdos3

end

end OAI
