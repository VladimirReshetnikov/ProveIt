/-
This file is generated.  Do not edit it directly.

Regenerate with `Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py` and verify with
`Algebra/PolynomialFormulas/Tools/generate_fin5_transitive_classification_certificates.py --check`.  Python supplies data only; every theorem
below is checked by Lean using ordinary kernel reduction.
-/

import PolynomialFormulas.Fin5TransitiveClassificationDoubleCosetCertificate
import PolynomialFormulas.Fin5TransitiveClassificationAffineGenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationAlternating0GenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationAlternating1GenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationSymmetric0GenerationCertificate
import PolynomialFormulas.Fin5TransitiveClassificationSymmetric1GenerationCertificate
import Mathlib.Tactic

namespace LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates

/-- Bounded replacement for the old 120-step all-generators computation. -/
theorem representative_generation_certificate (i : Fin 8) :
    generatedStage (representative i) (representativeDepth i) =
      classElements (representativeClass i) := by
  fin_cases i
  · exact cyclic_generation_certificate
  · exact dihedral_generation_certificate
  · exact frobenius0_generation_certificate
  · exact frobenius1_generation_certificate
  · exact alternating0_generation_certificate
  · exact alternating1_generation_certificate
  · exact symmetric0_generation_certificate
  · exact symmetric1_generation_certificate

theorem classElements_le_of_standardC5_le
    (H : Subgroup S5) (g : S5)
    (hC : standardC5 ≤ H) (hg : g ∈ H) :
    ∀ x : S5, x ∈ classElements (elementClass g) → x ∈ H := by
  obtain ⟨i, a, b, hdecomp, hclass⟩ :=
    exists_rotation_decomposition g
  have hrep : representative i ∈ H := by
    have hleft : fiveCycle ^ (a : ℕ) ∈ H :=
      Subgroup.pow_mem H (hC (Subgroup.mem_zpowers fiveCycle)) _
    have hright : fiveCycle ^ (b : ℕ) ∈ H :=
      Subgroup.pow_mem H (hC (Subgroup.mem_zpowers fiveCycle)) _
    have hcancel :
        (fiveCycle ^ (a : ℕ))⁻¹ * g *
            (fiveCycle ^ (b : ℕ))⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.inv_mem hleft) hg) (H.inv_mem hright)
    rw [hdecomp] at hcancel
    simpa [mul_assoc] using hcancel
  intro x hx
  rw [hclass] at hx
  rw [← representative_generation_certificate i] at hx
  exact generatedStage_subset_subgroup H (representative i)
    (hC (Subgroup.mem_zpowers fiveCycle)) hrep
    (representativeDepth i) x hx

end LeanProofs.PolynomialFormulas.Fin5TransitiveClassificationCertificates
