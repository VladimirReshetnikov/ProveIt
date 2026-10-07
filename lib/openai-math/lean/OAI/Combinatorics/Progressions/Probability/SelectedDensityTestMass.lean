import OAI.Combinatorics.Progressions.Lattices.SelectedResidueConstantMean
import OAI.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass

namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityMass_bound_of_constant_test
    {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (T : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus T V x)
    (D : (K × I → ℤ) → ℝ) {ε : ℝ}
    (htest : ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        ((1 : ℂ) * (D z : ℂ))) -
      ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) * 1‖ ≤ ε) :
    |selectedResidueDensityMass modulus T V D - 1| ≤ ε := by
  rw [selectedResidueSmoothPMF_const] at htest
  simp only [one_mul] at htest
  rw [← selectedResidueDensityMass_complex modulus T V hV hZ D,
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htest
  exact htest

end Erdos3

end

end OAI
