import OAI.Combinatorics.Progressions.Fourier.OneSiteFourierAverage

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

theorem layeredSiteWeight_oneSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (φ : (I → ℝ) → ℂ)
    (b : Option K → I → ℝ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s) (fun _ => φ) b =
      φ (integerSiteValue (affineSite root difference ∅) b) := by
  simp only [layeredSiteWeight, map_zero, AddCircle.coe_zero,
    CircleFourier.character_zero, one_mul]
  exact Fintype.prod_subsingleton
    (fun s : Finset (Fin 0) => φ (integerSiteValue (affineSite root difference s) b))
    (∅ : Finset (Fin 0))

end Erdos3.BooleanCubeKernel

end

end OAI
