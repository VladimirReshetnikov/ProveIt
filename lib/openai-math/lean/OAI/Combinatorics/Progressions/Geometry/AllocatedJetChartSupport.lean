import OAI.Combinatorics.Progressions.Estimates.AllocatedLongMixedCoefficientBound
import OAI.Combinatorics.Progressions.Lattices.MixedArrayIntegerImage

namespace OAI

section

namespace Erdos3

open Module Submodule
open scoped BigOperators Matrix

theorem boundedCoefficientJetMatrix_scaled_entry_bound {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O] [DecidableEq O]
    (root : K → ℤ) (A : Matrix α K ℤ) (T : K → ℝ) (hT : ∀ k, 0 < T k)
    (hroot : ∀ k, |(root k : ℝ) / T k| ≤ 1)
    (hA : ∀ i k, |(A i k : ℝ) / T k| ≤ 1)
    (h : ℕ) (rows : O → Finset α) (o : O) (e : VectorPolynomial.BoundedCoefficientExponent K h) :
    |(boundedCoefficientJetMatrix root A h rows o e : ℝ)| / monomialScale T e.val ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ h := by
  let e' := boundedCoefficientIntegerExponentEquiv K h e
  have he := congrFun (congrFun (normalizedBoundedIntegerJetMatrix_eq root A h rows T
    (H := 1) one_ne_zero) o) e'
  rw [normalizedIntegerColumns_entry_div] at he
  have hb := boundedDegreeRealJetMatrix_entry_bound _ _ hroot hA h rows o e'
  rw [← he] at hb
  change |(boundedDegreeIntegerJetMatrix root A h rows o e' : ℝ)| / monomialScale T e'.val ≤ _
  simpa only [div_one, mul_one_div, abs_div, abs_of_pos (monomialScale_pos T hT e'.val)] using hb

namespace VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedLayerSupported_jet_quarter {α : Type*} [Fintype α] [DecidableEq α]
    {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
    (root : LayerSamplerVariables G I n B → ℤ)
    (A : Matrix α (LayerSamplerVariables G I n B) ℤ) (rows : ∀ j, O j → Finset α)
    (hroot : ∀ k, |(root k : ℝ) / layerSamplerBox B U b S k| ≤ 1)
    (hA : ∀ i k, |(A i k : ℝ) / layerSamplerBox B U b S k| ≤ 1)
    (hσ1 : ∀ j, σ j ≤ 1) (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * R j)) ≤ 1 / 4)
    (j : Fin m) (a)
    (ha : mixedArraySupported (allocatedLayerCenters B U b S j) (allocatedLayerWidths B U b S j)
      (allocatedLayerIntegerPMFs B U b hR hσ S j) a) (t : O j) (i : J j) :
    |normalizedLatticePoint (euclideanSubspace (U j)) (b j)
      (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _
        (mixedArrayIntegerImage (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) a) t)) i| ≤ 1 / 4 := by
  classical
  let T := layerSamplerBox B U b S
  let Q := C j * (((Fintype.card (I j) : ℝ) + 1) * R j)
  let M := (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)
  have hT (k) : 0 < T k := lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k)
  have hQ : 0 ≤ Q := mul_nonneg (hC j) (mul_nonneg (by positivity) (hR j).le)
  have hc (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      |mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a e i| ≤ Q / monomialScale T e.val := by
    have h := allocatedLayerCoefficient_scaled_bounds B U b hR hσ S hσ1 j a ha e
    exact mixedRealPoint_scaled_coordinate_bound _ (b j) (o j) (hC j) (hR j).le
      (monomialScale_pos T hT e.val) (hchart j) _ _ h.1 h.2 i
  have hterm (e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) :
      |(boundedCoefficientJetMatrix root A (j.val + 1) (rows j) t e : ℝ) *
        mixedLiftCoefficient (euclideanSubspace (U j)) (b j) (o j) a e i| ≤ M * Q := by
    rw [abs_mul]
    calc
      _ ≤ |(boundedCoefficientJetMatrix root A (j.val + 1) (rows j) t e : ℝ)| *
          (Q / monomialScale T e.val) := mul_le_mul_of_nonneg_left (hc e) (abs_nonneg _)
      _ = (|(boundedCoefficientJetMatrix root A (j.val + 1) (rows j) t e : ℝ)| /
          monomialScale T e.val) * Q := by ring
      _ ≤ M * Q := mul_le_mul_of_nonneg_right
        (boundedCoefficientJetMatrix_scaled_entry_bound root A T hT hroot hA _ (rows j) t e) hQ
  have he := congrArg (fun v : EuclideanSpace ℝ (J j) => v i)
    (mixedArrayIntegerImage_point (euclideanSubspace (U j)) (b j) (o j)
      (boundedCoefficientJetMatrix root A (j.val + 1) (rows j)) a t)
  change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : J j => ℝ) i) _ at he
  rw [map_sum] at he
  simp only [map_zsmul, zsmul_eq_mul] at he
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _e : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1), M * Q :=
      Finset.sum_le_sum (fun e _ => hterm e)
    _ = (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) * M * Q := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
    _ ≤ 1 / 4 := hsmall j

end VectorPolynomial
end Erdos3

end

end OAI
