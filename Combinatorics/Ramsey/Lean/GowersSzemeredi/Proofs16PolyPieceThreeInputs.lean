import GowersSzemeredi.Proofs16PolyFamilyThree
import GowersSzemeredi.Proofs16ProductTranslate

/-! Inputs of a three-dimensional piece (Notes L.5, D3).

For `k = 2` the remainder of Gowers's identity is
`φ″ = V_{tf} + V_{ft} − V_{ff}` (`section16PhiRemainder_two`), where
`V_e(h, x) = φ(x₀ + e·h, x)` are the translated vertices. In the original frame
`w = (x₀ + h, x)`, each vertex is a face function:
* `V_{tf} = g₁(dropMid w)` with `g₁ = (midFace3 x₀).pullback φ`,
  `g₁(a, x) = φ(a, x₀¹, x)`;
* `V_{ft} = g₂(dropFirst w)` with `g₂ = (firstFace3 x₀).pullback φ`,
  `g₂(b, x) = φ(x₀⁰, b, x)`;
* `V_{ff} = g₃(lastPt3 w)` with `g₃ = (lastFace3 x₀).pullback φ`,
  `g₃(x) = φ(x₀⁰, x₀¹, x)`.

The faces are explicit `CoordinateFace`s, so their pullbacks inherit the
product property (`HasProductProperty.coordinateFace`). The deletion counts
`card_*_bad_le` bound the points whose projections leave a good set. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### The remainder at `k = 2` -/

/-- The vertex `tf`. -/
def vTF : Fin 2 → Bool := ![true, false]
/-- The vertex `ft`. -/
def vFT : Fin 2 → Bool := ![false, true]

theorem section16PhiRemainder_two {N : Nat} [NeZero N] (phi : Point N 3 → ZMod N)
    (x0 : Point N 2) (z : Point N 3) :
    section16PhiRemainder phi x0 z = section16TranslatedVertex phi x0 vTF z +
      section16TranslatedVertex phi x0 vFT z - section16TranslatedVertex phi x0 (fun _ => false) z := by
  unfold section16PhiRemainder
  rw [show (Finset.univ.filter fun e : Fin 2 → Bool => e ≠ fun _ => true) =
      {fun _ => false, vTF, vFT} by decide]
  have h1 : (fun _ : Fin 2 => false) ∉ ({vTF, vFT} : Finset (Fin 2 → Bool)) := by decide
  have h2 : vTF ∉ ({vFT} : Finset (Fin 2 → Bool)) := by decide
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  have w0 : boolWeight (fun _ : Fin 2 => false) = 0 := by simp [boolWeight, countWhere]
  have w1 : boolWeight vTF = 1 := by
    unfold vTF; simp [boolWeight, countWhere, Finset.card_filter, Fin.sum_univ_two]
  have w2 : boolWeight vFT = 1 := by
    unfold vFT; simp [boolWeight, countWhere, Finset.card_filter, Fin.sum_univ_two]
  rw [w0, w1, w2]
  ring

/-! ### The three faces -/

/-- The face `(a, x) ↦ (a, x₀¹, x)`. -/
def midFace3 {N : Nat} (x0 : Point N 2) : CoordinateFace N 3 2 where
  free := ⟨![0, 2], by decide⟩
  anchor := ![0, x0 1, 0]
  map y := ![y 0, x0 1, y 1]
  map_free := by
    intro y i
    fin_cases i <;> rfl
  map_fixed := by
    intro y j hj
    fin_cases j
    · exact absurd rfl (hj 0)
    · rfl
    · exact absurd rfl (hj 1)

/-- The face `(b, x) ↦ (x₀⁰, b, x)`. -/
def firstFace3 {N : Nat} (x0 : Point N 2) : CoordinateFace N 3 2 where
  free := ⟨![1, 2], by decide⟩
  anchor := ![x0 0, 0, 0]
  map y := ![x0 0, y 0, y 1]
  map_free := by
    intro y i
    fin_cases i <;> rfl
  map_fixed := by
    intro y j hj
    fin_cases j
    · rfl
    · exact absurd rfl (hj 0)
    · exact absurd rfl (hj 1)

/-- The face `x ↦ (x₀⁰, x₀¹, x)`. -/
def lastFace3 {N : Nat} (x0 : Point N 2) : CoordinateFace N 3 1 where
  free := ⟨![2], by decide⟩
  anchor := ![x0 0, x0 1, 0]
  map y := ![x0 0, x0 1, y 0]
  map_free := by
    intro y i
    fin_cases i; rfl
  map_fixed := by
    intro y j hj
    fin_cases j
    · rfl
    · rfl
    · exact absurd rfl (hj 0)

/-- The original-frame point of a translated point. -/
def origPt {N : Nat} (x0 : Point N 2) (z : Point N 3) : Point N 3 :=
  appendCoordinate (section16Init z + x0) (section16Last z)

theorem midFace3_map {N : Nat} (x0 : Point N 2) (z : Point N 3) :
    (midFace3 x0).map (dropMid (origPt x0 z)) =
      appendCoordinate (fun i => x0 i + if vTF i then section16Init z i else 0) (section16Last z) := by
  funext j
  fin_cases j <;>
    simp [midFace3, dropMid, origPt, vTF, appendCoordinate, section16Init, section16Last, add_comm]

theorem firstFace3_map {N : Nat} (x0 : Point N 2) (z : Point N 3) :
    (firstFace3 x0).map (dropFirst (origPt x0 z)) =
      appendCoordinate (fun i => x0 i + if vFT i then section16Init z i else 0) (section16Last z) := by
  funext j
  fin_cases j <;>
    simp [firstFace3, dropFirst, origPt, vFT, appendCoordinate, section16Init, section16Last, add_comm]

theorem lastFace3_map {N : Nat} (x0 : Point N 2) (z : Point N 3) :
    (lastFace3 x0).map (lastPt3 (origPt x0 z)) =
      appendCoordinate (fun i => x0 i + if (fun _ : Fin 2 => false) i then section16Init z i else 0)
        (section16Last z) := by
  funext j
  fin_cases j <;>
    simp [lastFace3, lastPt3, origPt, appendCoordinate, section16Last]

/-- The translated vertices as face functions of the original-frame point. -/
theorem translatedVertex_two_faces {N : Nat} (phi : Point N 3 → ZMod N) (x0 : Point N 2)
    (z : Point N 3) :
    section16TranslatedVertex phi x0 vTF z = (midFace3 x0).pullback phi (dropMid (origPt x0 z)) ∧
      section16TranslatedVertex phi x0 vFT z =
        (firstFace3 x0).pullback phi (dropFirst (origPt x0 z)) ∧
      section16TranslatedVertex phi x0 (fun _ => false) z =
        (lastFace3 x0).pullback phi (lastPt3 (origPt x0 z)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold CoordinateFace.pullback; rw [midFace3_map]; rfl
  · unfold CoordinateFace.pullback; rw [firstFace3_map]; rfl
  · unfold CoordinateFace.pullback; rw [lastFace3_map]; rfl

/-! ### Deletion counts -/

theorem origPt_init {N : Nat} (x0 : Point N 2) (z : Point N 3) :
    section16Init (origPt x0 z) = section16Init z + x0 := by
  unfold origPt; exact section16Init_appendCoordinate _ _

theorem origPt_last {N : Nat} (x0 : Point N 2) (z : Point N 3) :
    section16Last (origPt x0 z) = section16Last z := by
  unfold origPt; exact section16Last_appendCoordinate _ _

theorem card_init_bad_le {N : Nat} [NeZero N] {theta : Real} (x0 : Point N 2)
    (J : Finset (Point N 2)) (hJ : (1 - theta) * (N : Real) ^ 2 ≤ J.card) :
    (((Finset.univ : Finset (Point N 3)).filter fun z =>
      section16Init (origPt x0 z) ∉ J).card : Real) ≤ theta * (N : Real) ^ 3 := by
  have h := card_filter_selected_not_mem_le (n := 3) (l := 2)
    ⟨Fin.castSucc, Fin.castSucc_injective 2⟩ x0 J hJ (by omega)
  have hfun : ∀ z : Point N 3,
      (fun i => z ((⟨Fin.castSucc, Fin.castSucc_injective 2⟩ : Fin 2 ↪ Fin 3) i) + x0 i) =
        section16Init (origPt x0 z) := fun z => by
    rw [origPt_init]; funext i; simp [section16Init]
  simp only [hfun] at h
  exact h

theorem card_dropMid_bad_le {N : Nat} [NeZero N] {theta : Real} (x0 : Point N 2)
    (J : Finset (Point N 2)) (hJ : (1 - theta) * (N : Real) ^ 2 ≤ J.card) :
    (((Finset.univ : Finset (Point N 3)).filter fun z =>
      dropMid (origPt x0 z) ∉ J).card : Real) ≤ theta * (N : Real) ^ 3 := by
  have h := card_filter_selected_not_mem_le (n := 3) (l := 2) ⟨![0, 2], by decide⟩
    ![x0 0, 0] J hJ (by omega)
  have hfun : ∀ z : Point N 3,
      (fun i => z ((⟨![0, 2], by decide⟩ : Fin 2 ↪ Fin 3) i) + (![x0 0, 0] : Point N 2) i) =
        dropMid (origPt x0 z) := fun z => by
    funext i
    fin_cases i <;> simp [dropMid, origPt, appendCoordinate, section16Init, section16Last, add_comm]
  simp only [hfun] at h
  exact h

theorem card_dropFirst_bad_le {N : Nat} [NeZero N] {theta : Real} (x0 : Point N 2)
    (J : Finset (Point N 2)) (hJ : (1 - theta) * (N : Real) ^ 2 ≤ J.card) :
    (((Finset.univ : Finset (Point N 3)).filter fun z =>
      dropFirst (origPt x0 z) ∉ J).card : Real) ≤ theta * (N : Real) ^ 3 := by
  have h := card_filter_selected_not_mem_le (n := 3) (l := 2) ⟨![1, 2], by decide⟩
    ![x0 1, 0] J hJ (by omega)
  have hfun : ∀ z : Point N 3,
      (fun i => z ((⟨![1, 2], by decide⟩ : Fin 2 ↪ Fin 3) i) + (![x0 1, 0] : Point N 2) i) =
        dropFirst (origPt x0 z) := fun z => by
    funext i
    fin_cases i <;> simp [dropFirst, origPt, appendCoordinate, section16Init, section16Last, add_comm]
  simp only [hfun] at h
  exact h

theorem card_lastPt3_bad_le {N : Nat} [NeZero N] {theta : Real} (x0 : Point N 2)
    (J : Finset (Point N 1)) (hJ : (1 - theta) * (N : Real) ^ 1 ≤ J.card) :
    (((Finset.univ : Finset (Point N 3)).filter fun z =>
      lastPt3 (origPt x0 z) ∉ J).card : Real) ≤ theta * (N : Real) ^ 3 := by
  have h := card_filter_selected_not_mem_le (n := 3) (l := 1) ⟨![2], by decide⟩
    0 J hJ (by omega)
  have hfun : ∀ z : Point N 3,
      (fun i => z ((⟨![2], by decide⟩ : Fin 1 ↪ Fin 3) i) + (0 : Point N 1) i) =
        lastPt3 (origPt x0 z) := fun z => by
    funext i
    fin_cases i
    simp [lastPt3, origPt, appendCoordinate, section16Last]
  simp only [hfun] at h
  exact h

end LeanProofs.GowersSzemeredi
