/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedIdealSiteReconstruction

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedLongAmbientCoordinates (z : JetAmbientIndex O J → ℝ) : output → ℝ
  | ⟨⟨⟨j, .inl i⟩, _⟩, t⟩ => (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))).1 i
  | ⟨⟨⟨j, .inr i⟩, _⟩, t⟩ => (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))).2 i

omit [∀ j, Fintype (O j)] in
theorem allocatedLongAmbientCoordinates_point
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedLongAmbientCoordinates B U b S o (mixedJetAmbientPoint U b o z) =
      allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z a.val) := by
  funext a
  rcases a with ⟨⟨⟨j, i | i⟩, ha⟩, t⟩
  · change (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm ((EuclideanSpace.equiv (J j) ℝ)
        (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) t)))))).1 i = _
    rw [ContinuousLinearEquiv.symm_apply_apply, mixedRealCoordinates_integer]
    rfl
  · change (mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
      ((EuclideanSpace.equiv (J j) ℝ).symm ((EuclideanSpace.equiv (J j) ℝ)
        (normalizedLatticePoint (euclideanSubspace (U j)) (b j)
          (orthonormalMixedChart (o j) (mixedArrayRegroup _ _ _ (z j) t)))))).2 i = _
    rw [ContinuousLinearEquiv.symm_apply_apply, mixedRealCoordinates_integer]
    rfl

theorem allocatedLongAmbientCoordinates_lipschitz (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖) :
    LipschitzWith (∑ j, C j * Fintype.card (J j)) (allocatedLongAmbientCoordinates B U b S (O := O) o) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  rcases a with ⟨⟨⟨j, i⟩, ha⟩, t⟩
  have hrow := ((mixedRealCoordinates_lipschitz (euclideanSubspace (U j)) (b j) (o j) (hC j)).comp
    (euclideanFromCoordinates_lipschitz (D := J j))).dist_le_mul
      (fun k => z ⟨j, t, k⟩) (fun k => w ⟨j, t, k⟩)
  have hin : dist (fun k => z ⟨j, t, k⟩) (fun k => w ⟨j, t, k⟩) ≤ dist z w :=
    (dist_pi_le_iff dist_nonneg).mpr (fun k => dist_le_pi_dist z w ⟨j, t, k⟩)
  let pz := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
    ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => z ⟨j, t, k⟩))
  let pw := mixedRealCoordinates (euclideanSubspace (U j)) (b j) (o j)
    ((EuclideanSpace.equiv (J j) ℝ).symm (fun k => w ⟨j, t, k⟩))
  have hout : dist (allocatedLongAmbientCoordinates B U b S o z ⟨⟨⟨j, i⟩, ha⟩, t⟩)
      (allocatedLongAmbientCoordinates B U b S o w ⟨⟨⟨j, i⟩, ha⟩, t⟩) ≤ dist pz pw := by
    cases i with
    | inl i => exact (dist_le_pi_dist pz.1 pw.1 i).trans (le_max_left _ _)
    | inr i => exact (dist_le_pi_dist pz.2 pw.2 i).trans (le_max_right _ _)
  have hc : C j * Fintype.card (J j) ≤ ∑ j, C j * Fintype.card (J j) :=
    Finset.single_le_sum (f := fun k => C k * Fintype.card (J k))
      (fun _ _ => by positivity) (Finset.mem_univ j)
  exact (hout.trans hrow).trans ((mul_le_mul_of_nonneg_right
    (by exact_mod_cast hc) (dist_nonneg (x := z) (y := w))).trans'
      (mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "single" => (fun _ : Fin m => Unit)
local notation "grid" => allocatedGridAxis (I := I) U b S.value

noncomputable def allocatedAmbientSiteCoordinates
    (z : JetAmbientIndex single J → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a => if h : ¬grid a then
    allocatedLongAmbientCoordinates B U b S o z ⟨⟨a, h⟩, ()⟩ / R a.1 else 0

theorem allocatedAmbientSiteCoordinates_point
    (z : ∀ j, (I j → Unit → ℝ) × (Fin (n j) → Unit → ℤ)) :
    allocatedAmbientSiteCoordinates B U b S o (mixedJetAmbientPoint U b o z) =
      allocatedNormalizedMixedSiteValue B U b S (fun j => mixedArrayRegroup _ _ _ (z j) ()) := by
  funext a
  rcases a with ⟨j, i | i⟩
  · by_cases h : grid ⟨j, Sum.inl i⟩
    · simp only [allocatedAmbientSiteCoordinates, allocatedNormalizedMixedSiteValue, h,
        not_true_eq_false, dite_false, ite_true]
    · simp only [allocatedAmbientSiteCoordinates, allocatedNormalizedMixedSiteValue, h,
        not_false_eq_true, dite_true, ite_false, allocatedLongAmbientCoordinates_point]
      rfl
  · by_cases h : grid ⟨j, Sum.inr i⟩
    · simp only [allocatedAmbientSiteCoordinates, allocatedNormalizedMixedSiteValue, h,
        not_true_eq_false, dite_false, ite_true]
    · simp only [allocatedAmbientSiteCoordinates, allocatedNormalizedMixedSiteValue, h,
        not_false_eq_true, dite_true, ite_false, allocatedLongAmbientCoordinates_point]
      rfl

theorem allocatedAmbientSiteCoordinates_lipschitz (hR : ∀ j, 0 < R j)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (K * ∑ j, C j * Fintype.card (J j)) (allocatedAmbientSiteCoordinates B U b S o) := by
  have hlong := allocatedLongAmbientCoordinates_lipschitz B U b S (O := single) o C hC
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).mpr
  intro a
  by_cases h : ¬grid a
  · have hd := (dist_le_pi_dist (allocatedLongAmbientCoordinates B U b S o z)
        (allocatedLongAmbientCoordinates B U b S o w) ⟨⟨a, h⟩, ()⟩).trans (hlong.dist_le_mul z w)
    simp only [allocatedAmbientSiteCoordinates, dite_eq_left h, Real.dist_eq, ← sub_div,
      abs_div, abs_of_pos (hR a.1)]
    rw [Real.dist_eq] at hd
    calc
      _ ≤ (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) / R a.1 :=
        div_le_div_of_nonneg_right hd (hR a.1).le
      _ = (R a.1)⁻¹ * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) := by ring
      _ ≤ (K : ℝ) * (((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) * dist z w) :=
        mul_le_mul_of_nonneg_right (hK a.1) (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)
      _ = _ := by simp only [NNReal.coe_mul]; ring
  · simp only [allocatedAmbientSiteCoordinates, dite_eq_right h, dist_self]
    positivity

end Erdos3.VectorPolynomial

end

end OAI
