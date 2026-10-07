import GowersSzemeredi.Proofs16FaceInduction

/-! Parallel coordinate faces form an exact partition. Local restrictions
can therefore be assembled without overcounting their deletion losses. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def splitCoordinateFace {N d l r : Nat} (e : Fin d ≃ Fin l ⊕ Fin r)
    (z : Point N r) : CoordinateFace N d l where
  free := ⟨fun i => e.symm (Sum.inl i), fun _ _ h => Sum.inl_injective (e.symm.injective h)⟩
  anchor := fun j => Sum.elim (fun _ => 0) z (e j)
  map := fun x j => Sum.elim x z (e j)
  map_free := by intro x i; simp
  map_fixed := by
    intro x j hj
    cases he : e j with
    | inl i => exact (hj i (by apply e.injective; simpa using he.symm)).elim
    | inr i => simp

theorem splitCoordinateFace_map_eq_iff {N d l r : Nat}
    (e : Fin d ≃ Fin l ⊕ Fin r) (z w : Point N r) (x y : Point N l) :
    (splitCoordinateFace e z).map x = (splitCoordinateFace e w).map y ↔ x = y ∧ z = w := by
  constructor
  · intro h
    constructor
    · funext i
      have hh := congrFun h (e.symm (Sum.inl i))
      simpa [splitCoordinateFace] using hh
    · funext i
      have hh := congrFun h (e.symm (Sum.inr i))
      simpa [splitCoordinateFace] using hh
  · rintro ⟨rfl, rfl⟩
    rfl

def parallelFaceUnion {N d l r : Nat} [NeZero N] (e : Fin d ≃ Fin l ⊕ Fin r)
    (C : Point N r → Finset (Point N l)) : Finset (Point N d) :=
  Finset.univ.biUnion fun z => (C z).image (splitCoordinateFace e z).map

theorem splitCoordinateFace_domain_union {N d l r : Nat} [NeZero N]
    (e : Fin d ≃ Fin l ⊕ Fin r) (C : Point N r → Finset (Point N l)) (z : Point N r) :
    (splitCoordinateFace e z).domain (parallelFaceUnion e C) = C z := by
  classical
  ext x
  rw [CoordinateFace.mem_domain]
  simp only [parallelFaceUnion, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨w, y, hy, heq⟩
    obtain ⟨rfl, rfl⟩ := (splitCoordinateFace_map_eq_iff e w z y x).mp heq
    exact hy
  · intro hx
    exact ⟨z, x, hx, rfl⟩

theorem parallelFaceUnion_subset {N d l r : Nat} [NeZero N]
    (e : Fin d ≃ Fin l ⊕ Fin r) (B : Finset (Point N d))
    (C : Point N r → Finset (Point N l))
    (hC : ∀ z, C z ⊆ (splitCoordinateFace e z).domain B) : parallelFaceUnion e C ⊆ B := by
  classical
  intro x hx
  obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
  exact (CoordinateFace.mem_domain _ _ _).mp (hC z hy)

theorem parallelFaceUnion_card {N d l r : Nat} [NeZero N]
    (e : Fin d ≃ Fin l ⊕ Fin r) (C : Point N r → Finset (Point N l)) :
    (parallelFaceUnion e C).card = ∑ z, (C z).card := by
  classical
  unfold parallelFaceUnion
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro z _
    exact Finset.card_image_of_injective _ (CoordinateFace.map_injective _)
  · intro z _ w _ hzw
    apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hb
    exact hzw ((splitCoordinateFace_map_eq_iff e z w x y).mp (hx.trans hy.symm)).2

theorem parallelFaceUnion_domains {N d l r : Nat} [NeZero N]
    (e : Fin d ≃ Fin l ⊕ Fin r) (B : Finset (Point N d)) :
    parallelFaceUnion e (fun z => (splitCoordinateFace e z).domain B) = B := by
  classical
  apply Finset.Subset.antisymm (parallelFaceUnion_subset e B _ (fun _ => le_rfl))
  intro x hx
  let z : Point N r := fun i => x (e.symm (Sum.inr i))
  let y : Point N l := fun i => x (e.symm (Sum.inl i))
  have hmap : (splitCoordinateFace e z).map y = x := by
    funext i
    dsimp [splitCoordinateFace]
    cases he : e i with
    | inl j =>
      change x (e.symm (Sum.inl j)) = x i
      rw [← he, e.symm_apply_apply]
    | inr j =>
      change x (e.symm (Sum.inr j)) = x i
      rw [← he, e.symm_apply_apply]
  apply Finset.mem_biUnion.mpr
  refine ⟨z, Finset.mem_univ _, Finset.mem_image.mpr ⟨y, ?_, hmap⟩⟩
  exact (CoordinateFace.mem_domain _ _ _).mpr (hmap.symm ▸ hx)

theorem sum_coordinateFace_card {N d l r : Nat} [NeZero N]
    (e : Fin d ≃ Fin l ⊕ Fin r) (B : Finset (Point N d)) :
    ∑ z, ((splitCoordinateFace e z).domain B).card = B.card := by
  rw [← parallelFaceUnion_card, parallelFaceUnion_domains]

end LeanProofs.GowersSzemeredi
