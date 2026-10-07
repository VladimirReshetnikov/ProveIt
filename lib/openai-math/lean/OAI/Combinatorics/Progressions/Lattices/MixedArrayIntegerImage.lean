import OAI.Combinatorics.Progressions.Geometry.MixedArraySourceSupport

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

variable {D I J O Z : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}

noncomputable def mixedArrayIntegerImage (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) : (I → O → ℝ) × (Z → O → ℤ) :=
  (fun i => (A.map (Int.cast : ℤ → ℝ)) *ᵥ x.1 i, fun z => A *ᵥ x.2 z)

omit [Fintype I] in
theorem mixedArrayIntegerImage_regroup (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Z → J → ℤ)) (r : O) :
    mixedArrayRegroup I Z O (mixedArrayIntegerImage A x) r =
      ∑ j, A r j • mixedArrayRegroup I Z J x j := by
  apply Prod.ext
  · funext i
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.fst_sum,
      Finset.sum_apply]
    change (∑ j, (A r j : ℝ) * x.1 i j) = ∑ j, A r j • x.1 i j
    exact Finset.sum_congr rfl (fun j _ => Int.cast_smul_eq_zsmul ℝ (A r j) (x.1 i j))
  · funext z
    simp only [mixedArrayIntegerImage, mixedArrayRegroup_apply, Prod.snd_sum,
      Finset.sum_apply]
    change (∑ j, A r j * x.2 z j) = ∑ j, A r j • x.2 z j
    simp only [smul_eq_mul]

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
variable (o : OrthonormalBasis I ℝ W)

theorem mixedArrayIntegerImage_quotient [Fintype O] (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Fin n → J → ℤ)) (r : O) :
    mixedArrayQuotient W b hb o (mixedArrayIntegerImage A x) r =
      ∑ j, A r j • mixedArrayQuotient W b hb o x j := by
  unfold mixedArrayQuotient
  rw [mixedArrayIntegerImage_regroup]
  rw [orthonormalMixedChart_sum_zsmul, normalizedLatticeQuotient_sum_zsmul]

theorem mixedArrayIntegerImage_point (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Fin n → J → ℤ)) (r : O) :
    normalizedLatticePoint W b (orthonormalMixedChart o
      (mixedArrayRegroup I (Fin n) O (mixedArrayIntegerImage A x) r)) =
      ∑ j, A r j • normalizedLatticePoint W b
        (orthonormalMixedChart o (mixedArrayRegroup I (Fin n) J x j)) := by
  rw [mixedArrayIntegerImage_regroup]
  rw [orthonormalMixedChart_sum_zsmul, normalizedLatticePoint_sum_zsmul]

theorem mixedArrayIntegerImage_unique [Fintype O] (A : Matrix O J ℤ)
    (x : (I → J → ℝ) × (Fin n → J → ℤ))
    (y : (I → O → ℝ) × (Fin n → O → ℤ))
    (hx : mixedArrayInChart W b o (mixedArrayIntegerImage A x))
    (hy : mixedArrayInChart W b o y)
    (hq : ∀ r, mixedArrayQuotient W b hb o y r =
      ∑ j, A r j • mixedArrayQuotient W b hb o x j) :
    y = mixedArrayIntegerImage A x := by
  apply mixedArrayQuotient_injOn_chart W b hb o hy hx
  exact funext (fun r => (hq r).trans (mixedArrayIntegerImage_quotient W b hb o A x r).symm)

end Erdos3

end

end OAI
