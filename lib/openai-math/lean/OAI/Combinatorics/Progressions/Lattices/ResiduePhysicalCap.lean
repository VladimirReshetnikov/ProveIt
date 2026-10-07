import OAI.Combinatorics.Progressions.Estimates.PhysicalBaseInjection

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem residueSmoothPMF_physical_cap {K I : Type*} [Fintype K] [Fintype I]
    (root : K → ℤ) (residue : Option K × I → ℤ)
    (modulus : I → ℕ) (hmodulus : ∀ i, 0 < modulus i)
    (W : Option K × I → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < shiftedSmoothProductMass (residueProfileCenter residue modulus) (residueProfileWidth modulus W))
    (hbase : ∀ i, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W (none,i))
    (y : I → ℝ) :
    ((residueSmoothPMF residue modulus hmodulus W hW hZ).map (physicalAffineSite root) y).toReal ≤
      ∏ i, 2*(modulus i : ℝ)/W (none,i) := by
  rw [residueSmoothPMF, PMF.map_comp, residueSmoothIndexPMF]
  have h := shiftedSmoothProductPMF_base_cap (residueProfileCenter residue modulus)
    (residueProfileWidth modulus W) (residueProfileWidth_pos modulus W hmodulus hW) hZ
    (physicalAffineSite root ∘ residueLatticeArray residue modulus)
    (physicalAffineSite_residue_base_injective root residue modulus hmodulus) hbase y
  simpa only [residueProfileWidth, div_div_eq_mul_div] using h

end Erdos3.BooleanCubeKernel

end

end OAI
