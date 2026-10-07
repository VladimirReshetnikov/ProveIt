/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.LinearAlgebra.StdBasis
import OAI.Combinatorics.Progressions.Polynomial.LowTaggedPolynomialCoordinates

namespace OAI

section

namespace Erdos3
open Module
open scoped BigOperators

variable {B R : Type*} [Fintype B] [Field R]

theorem pi_basisGradeProjection_apply (w : B → ℕ) (h : ℕ) (x : B → R) (i : B) :
    basisGradeProjection (Pi.basisFun R B) w h x i = if w i = h then x i else 0 := by
  simpa only [Pi.basisFun_repr] using
    basisGradeProjection_repr (Pi.basisFun R B) w h x i

theorem sum_positive_coordinate_grades
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (x : B → R) :
    (∑ h : Fin d, basisGradeProjection (Pi.basisFun R B) w (h.val + 1) x) = x := by
  classical
  funext i
  rw [Finset.sum_apply]
  simp_rw [pi_basisGradeProjection_apply]
  let hi : Fin d := ⟨w i - 1, by have := hw i; have := hwd i; omega⟩
  have he (h : Fin d) : w i = h.val + 1 ↔ h = hi := by
    dsimp only [hi]
    have := hw i
    constructor
    · intro hh
      apply Fin.ext
      change h.val = w i - 1
      omega
    · intro hh
      subst h
      change w i = (w i - 1) + 1
      omega
  simp_rw [he]
  simp

noncomputable def coordinateWeightLayer (w : B → ℕ) (K : Submodule R (B → R))
    (h : ℕ) : Submodule R (B → R) :=
  K.map (basisGradeProjection (Pi.basisFun R B) w h)

theorem coordinateWeightLayer_le (w : B → ℕ) (K : Submodule R (B → R))
    (hK : BasisGradedSubmodule (Pi.basisFun R B) w K) (h : ℕ) :
    coordinateWeightLayer w K h ≤ K := by
  rintro y ⟨x, hx, rfl⟩
  exact hK h x hx

theorem iSup_coordinateWeightLayer_eq
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (K : Submodule R (B → R)) (hK : BasisGradedSubmodule (Pi.basisFun R B) w K) :
    (⨆ h : Fin d, coordinateWeightLayer w K (h.val + 1)) = K := by
  apply le_antisymm
  · exact iSup_le fun h => coordinateWeightLayer_le w K hK (h.val + 1)
  · intro x hx
    rw [← sum_positive_coordinate_grades w d hw hwd x]
    apply Submodule.sum_mem
    intro h _
    exact (le_iSup (fun h : Fin d => coordinateWeightLayer w K (h.val + 1)) h)
      ⟨x, hx, rfl⟩

theorem coordinateWeightLayer_span {J : Type*}
    (w : B → ℕ) (g : J → B → R) (h : ℕ) :
    coordinateWeightLayer w (Submodule.span R (Set.range g)) h =
      Submodule.span R (Set.range (fun j i => if w i = h then g j i else 0)) := by
  rw [coordinateWeightLayer, Submodule.map_span, ← Set.range_comp]
  apply congrArg (Submodule.span R)
  congr 1
  funext j i
  exact pi_basisGradeProjection_apply w h (g j) i

theorem le_coordinateWeightLayer_of_supported
    (w : B → ℕ) (K W : Submodule R (B → R)) (h : ℕ) (hWK : W ≤ K)
    (hsupport : ∀ x ∈ W, ∀ i, w i ≠ h → x i = 0) :
    W ≤ coordinateWeightLayer w K h := by
  intro x hx
  refine ⟨x, hWK hx, ?_⟩
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : w i = h
  · simp only [ite_eq_left hi]
  · simp only [ite_eq_right hi, hsupport x hx i hi]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedSlot (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (k : J j) : Fin (Fintype.card (LowTaggedIndex J d)) :=
  Fintype.equivFin (LowTaggedIndex J d) ⟨⟨j, k⟩, hj⟩

@[simp] theorem lowTaggedIndex_slot (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (k : J j) : lowTaggedIndex J d (lowTaggedSlot J d j hj k) = ⟨j, k⟩ := by
  simp [lowTaggedIndex, lowTaggedSlot]

theorem lowTaggedSlot_injective (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    Function.Injective (lowTaggedSlot J d j hj) := by
  intro k l h
  have he := congrArg (lowTaggedIndex J d) h
  simpa using he

theorem lowTaggedSlot_eq_of_tag (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (i : Fin (Fintype.card (LowTaggedIndex J d)))
    (hi : (lowTaggedIndex J d i).1 = j) :
    ∃ k : J j, lowTaggedSlot J d j hj k = i := by
  let q := (Fintype.equivFin (LowTaggedIndex J d)).symm i
  have hq : q.val.1 = j := hi
  have hqi : Fintype.equivFin (LowTaggedIndex J d) q = i :=
    (Fintype.equivFin (LowTaggedIndex J d)).apply_symm_apply i
  obtain ⟨⟨j', k⟩, h⟩ := q
  dsimp at hq
  subst j'
  exact ⟨k, hqi⟩

noncomputable def lowTaggedEmbedding (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    (J j → ℝ) →ₗ[ℝ] (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) := by
  classical
  exact ∑ k : J j,
    (LinearMap.single ℝ (fun _ : Fin (Fintype.card (LowTaggedIndex J d)) => ℝ)
      (lowTaggedSlot J d j hj k)).comp (LinearMap.proj k)

theorem lowTaggedEmbedding_apply (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (v : J j → ℝ) (i : Fin (Fintype.card (LowTaggedIndex J d))) :
    lowTaggedEmbedding J d j hj v i =
      ∑ k : J j, (Pi.single (lowTaggedSlot J d j hj k) (v k) :
        Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) i := by
  classical
  simp [lowTaggedEmbedding, LinearMap.sum_apply, Finset.sum_apply]

@[simp] theorem lowTaggedEmbedding_apply_slot (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ) (k : J j) :
    lowTaggedEmbedding J d j hj v (lowTaggedSlot J d j hj k) = v k := by
  classical
  rw [lowTaggedEmbedding_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro l _ hl
    exact Pi.single_eq_of_ne (fun he => hl
      ((lowTaggedSlot_injective J d j hj) he.symm)) _
  · simp

theorem lowTaggedEmbedding_injective (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    Function.Injective (lowTaggedEmbedding J d j hj) := by
  intro v w h
  funext k
  have hk := congrFun h (lowTaggedSlot J d j hj k)
  simpa only [lowTaggedEmbedding_apply_slot] using hk

theorem lowTaggedEmbedding_apply_of_ne (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ)
    (i : Fin (Fintype.card (LowTaggedIndex J d)))
    (hi : (lowTaggedIndex J d i).1 ≠ j) :
    lowTaggedEmbedding J d j hj v i = 0 := by
  classical
  rw [lowTaggedEmbedding_apply]
  apply Finset.sum_eq_zero
  intro k _
  apply Pi.single_eq_of_ne
  intro he
  apply hi
  rw [he, lowTaggedIndex_slot]

theorem lowTaggedEmbedding_pairing (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (a : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) (v : J j → ℝ) :
    (∑ i, a i * lowTaggedEmbedding J d j hj v i) =
      ∑ k : J j, a (lowTaggedSlot J d j hj k) * v k := by
  classical
  simp only [lowTaggedEmbedding, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.comp_apply, LinearMap.single_apply, LinearMap.proj_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp [Pi.single_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]

noncomputable def lowTaggedRestriction (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d) :
    (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) →ₗ[ℝ] (J j → ℝ) :=
  LinearMap.pi fun k => LinearMap.proj (lowTaggedSlot J d j hj k)

@[simp] theorem lowTaggedRestriction_apply (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (k : J j) :
    lowTaggedRestriction J d j hj z k = z (lowTaggedSlot J d j hj k) := rfl

@[simp] theorem lowTaggedRestriction_embedding (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (v : J j → ℝ) :
    lowTaggedRestriction J d j hj (lowTaggedEmbedding J d j hj v) = v := by
  funext k
  exact lowTaggedEmbedding_apply_slot J d j hj v k

theorem lowTaggedEmbedding_restriction (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ) :
    lowTaggedEmbedding J d j hj (lowTaggedRestriction J d j hj z) =
      basisGradeProjection (Pi.basisFun ℝ _) (lowTaggedWeight J d) (j.val + 1) z := by
  classical
  funext i
  rw [pi_basisGradeProjection_apply]
  by_cases hi : (lowTaggedIndex J d i).1 = j
  · obtain ⟨k, rfl⟩ := lowTaggedSlot_eq_of_tag J d j hj i hi
    simp [lowTaggedWeight]
  · have hw : lowTaggedWeight J d i ≠ j.val + 1 := by
      intro hw
      apply hi
      apply Fin.ext
      exact Nat.add_right_cancel hw
    rw [lowTaggedEmbedding_apply_of_ne J d j hj _ i hi, ite_eq_right hw]

theorem lowTagged_comap_eq_map (d : ℕ) (j : Fin m) (hj : j.val + 1 ≤ d)
    (K : Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J d)) → ℝ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d) K) :
    K.comap (lowTaggedEmbedding J d j hj) = K.map (lowTaggedRestriction J d j hj) := by
  apply le_antisymm
  · intro v hv
    exact ⟨lowTaggedEmbedding J d j hj v, hv,
      lowTaggedRestriction_embedding J d j hj v⟩
  · rintro v ⟨z, hz, rfl⟩
    change lowTaggedEmbedding J d j hj (lowTaggedRestriction J d j hj z) ∈ K
    rw [lowTaggedEmbedding_restriction]
    exact hK (j.val + 1) z hz

theorem lowTagged_comap_span_eq {A : Type*} (d : ℕ) (j : Fin m)
    (hj : j.val + 1 ≤ d)
    (g : A → Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
    (hg : BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
      (Submodule.span ℝ (Set.range g))) :
    (Submodule.span ℝ (Set.range g)).comap (lowTaggedEmbedding J d j hj) =
      Submodule.span ℝ (Set.range (fun a k => g a (lowTaggedSlot J d j hj k))) := by
  rw [lowTagged_comap_eq_map J d j hj _ hg, Submodule.map_span, ← Set.range_comp]
  rfl

end Erdos3.VectorPolynomial

end

end OAI
