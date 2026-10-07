import OAI.Combinatorics.Progressions.Geometry.MixedRealCoordinates
import OAI.Combinatorics.Progressions.Probability.ScaledArrayLaw

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators NNReal

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}

theorem euclideanFromCoordinates_lipschitz :
    LipschitzWith (Fintype.card D) (EuclideanSpace.equiv D ℝ).symm := by
  have hn (x : D → ℝ) : ‖(EuclideanSpace.equiv D ℝ).symm x‖ ≤ (Fintype.card D : ℝ) * ‖x‖ := by
    calc
      _ ≤ ∑ i, |x i| := euclidean_norm_le_sum_abs _
      _ ≤ ∑ _i : D, ‖x‖ := Finset.sum_le_sum (fun i _ => by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i)
      _ = _ := by simp
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact hn (x - y)

variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (o : OrthonormalBasis I ℝ W)

noncomputable def mixedDensityCovolumeRatio : ℝ :=
  ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) /
    ∏ i, (basisAxisScale b i : ℝ)

theorem mixedDensityCovolumeRatio_pos
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W)] :
    0 < mixedDensityCovolumeRatio W b :=
  div_pos (ZLattice.covolume_pos _ volume)
    (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i)))

noncomputable def mixedAmbientInterpolation (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (v : D → ℝ) : ℝ :=
  mixedDensityCovolumeRatio W b * mixedDensityInterpolation c w f
    (mixedRealCoordinates W b o ((EuclideanSpace.equiv D ℝ).symm v))

theorem mixedAmbientInterpolation_grid (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    (p : Fin n → PMF ℤ)
    (hf : ∀ i (k : ℤ), f i ((k : ℝ) / basisAxisScale b i) = basisAxisScale b i * (p i k).toReal)
    (u : I → ℝ) (z : Fin n → ℤ) :
    mixedAmbientInterpolation W b o c w f
      ((EuclideanSpace.equiv D ℝ) (normalizedLatticePoint W b (orthonormalMixedChart o (u, z)))) =
      ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) *
        mixedCoefficientDensity c w p (u, z) := by
  have hK : (∏ i, (basisAxisScale b i : ℝ)) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => Nat.cast_pos.mpr (basisAxisScale_pos b i)))
  rw [mixedAmbientInterpolation, ContinuousLinearEquiv.symm_apply_apply,
    mixedRealCoordinates_integer, mixedDensityInterpolation_grid c w f _ p hf,
    mixedDensityCovolumeRatio]
  field_simp [hK]

theorem mixedAmbientInterpolation_bounds (c w : I → ℝ) (f : Fin n → ℝ → ℝ)
    {M J C V : ℝ≥0}
    (hM : ∀ x, 0 ≤ mixedDensityInterpolation c w f x ∧ mixedDensityInterpolation c w f x ≤ M)
    (hJ : LipschitzWith J (mixedDensityInterpolation c w f))
    (hC : ∀ x, ‖normalizedOrthogonalChart W b x‖ ≤ C * ‖x‖)
    (hV : 0 ≤ mixedDensityCovolumeRatio W b ∧ mixedDensityCovolumeRatio W b ≤ V) :
    (∀ x, 0 ≤ mixedAmbientInterpolation W b o c w f x ∧
      mixedAmbientInterpolation W b o c w f x ≤ V * M) ∧
    LipschitzWith (V * (J * (C * Fintype.card D))) (mixedAmbientInterpolation W b o c w f) := by
  have hg := hJ.comp ((mixedRealCoordinates_lipschitz W b o hC).comp
    (euclideanFromCoordinates_lipschitz (D := D)))
  have hl := lipschitz_real_mul_of_bounds (Bf := V) (Bg := M)
    (fun _ : D → ℝ => mixedDensityCovolumeRatio W b)
    (fun x => mixedDensityInterpolation c w f
      (mixedRealCoordinates W b o ((EuclideanSpace.equiv D ℝ).symm x)))
    (LipschitzWith.const _) hg
    (fun _ => by rw [abs_of_nonneg hV.1]; exact hV.2)
    (fun x => by rw [abs_of_nonneg (hM _).1]; exact (hM _).2)
  refine ⟨?_, ?_⟩
  · intro x
    exact ⟨mul_nonneg hV.1 (hM _).1, mul_le_mul hV.2 (hM _).2 (hM _).1 V.coe_nonneg⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [mixedAmbientInterpolation, mul_zero, add_zero] using hl.dist_le_mul x y

end Erdos3

end

section

namespace Erdos3

open Module Submodule
open scoped BigOperators

theorem latticeSection_covolume_eq_one_of_isEmpty
    {D : Type*} [Fintype D] [IsEmpty D]
    (W : Submodule ℝ (EuclideanSpace ℝ D)) :
    ZLattice.covolume (latticeSection (standardEuclideanLattice D) W) = 1 := by
  let : IsZLattice ℝ (latticeSection (standardEuclideanLattice D) W) := by
    constructor
    apply eq_top_iff.mpr
    intro x _
    have hx : x = 0 := Subsingleton.elim _ _
    rw [hx]
    exact Submodule.zero_mem _
  exact lattice_covolume_of_finrank_zero _ (Module.finrank_zero_of_subsingleton)

theorem mixedDensityCovolumeRatio_eq_one_of_isEmpty
    {D : Type*} [Fintype D] [IsEmpty D] {n : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ) :
    mixedDensityCovolumeRatio W b = 1 := by
  have hn : Fintype.card (Fin n) = 0 :=
    (Module.finrank_eq_card_basis b).symm.trans Module.finrank_zero_of_subsingleton
  let : IsEmpty (Fin n) := Fintype.card_eq_zero_iff.mp hn
  simp [mixedDensityCovolumeRatio, latticeSection_covolume_eq_one_of_isEmpty W]

end Erdos3

end

end OAI
