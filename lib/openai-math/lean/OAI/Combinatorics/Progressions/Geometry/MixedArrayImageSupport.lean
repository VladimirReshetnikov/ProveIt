import OAI.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage

namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule
open scoped BigOperators Matrix

theorem mixedArrayIntegerImage_inChart {D I J O : Type*}
    [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
    (o : OrthonormalBasis I ℝ W) (A : Matrix O J ℤ)
    {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hchart : ∀ v, ‖(normalizedOrthogonalChart W b).symm v‖ ≤ C * ‖v‖)
    (hsmall : ∀ t, C * ((Fintype.card I : ℝ) + 1) * (∑ j, |(A t j : ℝ)| * R) ≤ 1 / 4)
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j)
    (hcw : ∀ i j, |c i j| + w i j ≤ R) (p : Fin n → J → PMF ℤ)
    (hp : ∀ z j k, k ∈ (p z j).support → |(k : ℝ) / basisAxisScale b z| ≤ R)
    (x : (I → J → ℝ) × (Fin n → J → ℤ)) (hx : mixedArraySupported c w p x) :
    mixedArrayInChart W b o (mixedArrayIntegerImage A x) := by
  have hs (j) := (mixedCoefficientDensity_support (fun i => c i j) (fun i => w i j)
    (fun z => p z j) (mixedArrayRegroup I (Fin n) J x j)).mp (hx j)
  have hbound (t) (v : J → ℝ) (hv : ∀ j, |v j| ≤ R) :
      |∑ j, (A t j : ℝ) * v j| ≤ ∑ j, |(A t j : ℝ)| * R := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hv j) (abs_nonneg _)
  intro t
  apply normalizedMixedPoint_small W b o hC
    (Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) hR)) hchart (hsmall t)
  · intro i
    exact hbound t (x.1 i) (fun j =>
      (affineProbabilityProfile_abs_le _ (hw i j) ((hs j).1 i)).trans (hcw i j))
  · intro z
    change |(((A *ᵥ x.2 z) t : ℤ) : ℝ) / basisAxisScale b z| ≤ _
    have he : (((A *ᵥ x.2 z) t : ℤ) : ℝ) / basisAxisScale b z =
        ∑ j, (A t j : ℝ) * ((x.2 z j : ℝ) / basisAxisScale b z) := by
      simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Finset.sum_div, mul_div_assoc]
    rw [he]
    exact hbound t _ (fun j => hp z j _ ((hs j).2 z))

end Erdos3

end

end OAI
