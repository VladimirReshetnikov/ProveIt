import OAI.Combinatorics.Progressions.Lattices.SelectedResidueApproximation

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {K X : Type*} [Fintype K] [Fintype X]
variable (modulus : X → ℕ) (hmodulus : ∀ x, 0 < modulus x)
variable (r : ColumnResiduePattern K X modulus)
variable (V : K × X → ℝ) (hV : ∀ z, 0 < V z)

include hmodulus hV in
theorem selectedResidueSmooth_singleton_mass :
    (∑' z, selectedResidueSmoothWeight modulus {r} V z) =
      shiftedSmoothProductMass (residueProfileCenter (columnResidueRepresentative modulus r) modulus)
        (residueProfileWidth modulus V) := by
  rw [residueSmoothWeight_mass _ modulus hmodulus V hV]
  apply tsum_congr
  intro z
  simp only [selectedResidueSmoothWeight, Finset.mem_singleton, residueSmoothWeight_eq_pattern]

include hmodulus hV in
theorem selectedResidueSmooth_singleton_indexMass_pos
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z) :
    0 < shiftedSmoothProductMass (residueProfileCenter (columnResidueRepresentative modulus r) modulus)
      (residueProfileWidth modulus V) := by
  rwa [← selectedResidueSmooth_singleton_mass modulus hmodulus r V hV]

theorem selectedResidueSmoothPMF_singleton_eq_residueSmooth
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z) :
    selectedResidueSmoothPMF modulus {r} V hV hZ =
      residueSmoothPMF (columnResidueRepresentative modulus r) modulus hmodulus V hV
        (selectedResidueSmooth_singleton_indexMass_pos modulus hmodulus r V hV hZ) := by
  ext z
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [selectedResidueSmoothPMF_toReal, residueSmoothPMF_conditional_weight]
  congr 1
  · simp only [selectedResidueSmoothWeight, Finset.mem_singleton, residueSmoothWeight_eq_pattern]
  · apply tsum_congr
    intro y
    simp only [selectedResidueSmoothWeight, Finset.mem_singleton, residueSmoothWeight_eq_pattern]

theorem selectedResidueSmoothPMF_singleton_normalized_expectation
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus {r} V z)
    (φ : (K × X → ℝ) → ℂ) :
    (∑' z, ((selectedResidueSmoothPMF modulus {r} V hV hZ z).toReal : ℂ) *
      φ (fun k => (z k : ℝ) / V k)) =
      ∑' z, ((shiftedSmoothProductPMF
        (residueProfileCenter (columnResidueRepresentative modulus r) modulus)
        (residueProfileWidth modulus V) (residueProfileWidth_pos modulus V hmodulus hV)
        (selectedResidueSmooth_singleton_indexMass_pos modulus hmodulus r V hV hZ) z).toReal : ℂ) *
        φ (rectangularLatticePoint (residueProfileCenter (columnResidueRepresentative modulus r) modulus)
          (residueProfileWidth modulus V) z) := by
  rw [selectedResidueSmoothPMF_singleton_eq_residueSmooth modulus hmodulus r V hV hZ,
    residueSmoothPMF_expectation]
  simp only [residueSmoothIndexPMF, residueProfile_point _ modulus hmodulus V hV]

end Erdos3

end

end OAI
