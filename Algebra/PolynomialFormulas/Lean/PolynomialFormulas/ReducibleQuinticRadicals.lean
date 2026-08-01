import PolynomialFormulas.LowDegreeRadicals
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Reducible quintics are solvable by radicals

A reducible monic quintic factors into two nonconstant rational polynomials.
Both factors have degree at most four, so the verified low-degree radical
theorem applies to whichever factor contains a given root.
-/

open Polynomial

namespace LeanProofs.PolynomialFormulas.ReducibleQuinticRadicals

open LowDegreeRadicals

/-- Every reducible monic rational quintic is completely solvable by
radicals. -/
theorem completelySolvableByRadicals_of_monic_natDegree_five_not_irreducible
    {P : ℚ[X]} (hmonic : P.Monic) (hdeg : P.natDegree = 5)
    (hred : ¬Irreducible P) : CompletelySolvableByRadicals P := by
  have hnonunit : ¬IsUnit P :=
    Polynomial.not_isUnit_of_natDegree_pos P (by omega)
  simp only [irreducible_iff, hnonunit] at hred
  push Not at hred
  obtain ⟨A, B, hAB, hAunit, hBunit⟩ := hred trivial
  have hAdiv : A ∣ P := ⟨B, hAB⟩
  have hBdiv : B ∣ P := ⟨A, by rw [mul_comm]; exact hAB⟩
  have hApos : 0 < A.natDegree :=
    Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hmonic hAunit hAdiv
  have hBpos : 0 < B.natDegree :=
    Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hmonic hBunit hBdiv
  have hA0 : A ≠ 0 := ne_zero_of_natDegree_gt hApos
  have hB0 : B ≠ 0 := ne_zero_of_natDegree_gt hBpos
  have hsum : A.natDegree + B.natDegree = 5 := by
    rw [← Polynomial.natDegree_mul hA0 hB0, ← hAB, hdeg]
  have hAle : A.natDegree ≤ 4 := by omega
  have hBle : B.natDegree ≤ 4 := by omega
  intro x
  have hxP : P.aeval (x : ℂ) = 0 :=
    aeval_eq_zero_of_mem_rootSet x.property
  have hxAB : A.aeval (x : ℂ) * B.aeval (x : ℂ) = 0 := by
    rw [← map_mul, ← hAB]
    exact hxP
  rcases mul_eq_zero.mp hxAB with hxA | hxB
  · let y : A.rootSet ℂ :=
      ⟨x, (mem_rootSet_of_ne hA0).2 hxA⟩
    exact root_mem_of_natDegree_le_four hAle y
  · let y : B.rootSet ℂ :=
      ⟨x, (mem_rootSet_of_ne hB0).2 hxB⟩
    exact root_mem_of_natDegree_le_four hBle y

end LeanProofs.PolynomialFormulas.ReducibleQuinticRadicals
