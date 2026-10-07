import GowersSzemeredi.Proofs16PermutedCovers
import GowersSzemeredi.Proofs16FiniteFaceInduction

/-! Coordinate directions are indexed by subsets of the ambient coordinates.
Each face is a reparameterized member of the corresponding parallel family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def coordinateDirectionSplit {d : Nat} (s : Finset (Fin d)) :
    Fin d ≃ Fin s.card ⊕ Fin sᶜ.card :=
  (Equiv.sumCompl (fun i => i ∈ s)).symm.trans
    (Equiv.sumCongr (s.equivFinOfCardEq rfl)
      ((Equiv.subtypeEquivRight (fun i => (Finset.mem_compl (s := s) (a := i)).symm)).trans
        (sᶜ.equivFinOfCardEq rfl)))

theorem coordinateDirectionSplit_symm_inl {d : Nat} (s : Finset (Fin d))
    (i : Fin s.card) :
    (coordinateDirectionSplit s).symm (Sum.inl i) = (s.equivFinOfCardEq rfl).symm i := rfl

theorem coordinateDirectionSplit_symm_inr {d : Nat} (s : Finset (Fin d))
    (i : Fin sᶜ.card) :
    (coordinateDirectionSplit s).symm (Sum.inr i) = (sᶜ.equivFinOfCardEq rfl).symm i := rfl

def CoordinateFace.direction {N d l : Nat} (F : CoordinateFace N d l) : Finset (Fin d) :=
  Finset.univ.image F.free

@[simp] theorem CoordinateFace.mem_direction {N d l : Nat} (F : CoordinateFace N d l)
    (j : Fin d) : j ∈ F.direction ↔ ∃ i, F.free i = j := by
  simp [CoordinateFace.direction]

@[simp] theorem CoordinateFace.direction_card {N d l : Nat} (F : CoordinateFace N d l) :
    F.direction.card = l := by
  rw [CoordinateFace.direction, Finset.card_image_of_injective _ F.free.injective]
  simp

def CoordinateFace.directionEquiv {N d l : Nat} (F : CoordinateFace N d l) :
    Fin l ≃ F.direction :=
  Equiv.ofBijective (fun i => ⟨F.free i, (F.mem_direction _).mpr ⟨i, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact F.free.injective (congrArg Subtype.val h)
    · intro j
      obtain ⟨i, hi⟩ := (F.mem_direction j).mp j.property
      exact ⟨i, Subtype.ext hi⟩)

/-- The ordering of a face's free coordinates differs from the chosen
ordering of its direction by an equivalence, without changing its image. -/
theorem CoordinateFace.parallel_reparametrization {N d l : Nat} (F : CoordinateFace N d l) :
    ∃ (e : Fin F.direction.card ≃ Fin l) (z : Point N F.directionᶜ.card),
      ∀ x, F.map x = (splitCoordinateFace (coordinateDirectionSplit F.direction) z).map
        (fun i => x (e i)) := by
  let t := F.direction.equivFinOfCardEq rfl
  let e := t.symm.trans F.directionEquiv.symm
  let a := coordinateDirectionSplit F.direction
  let z : Point N F.directionᶜ.card := fun i => F.anchor (a.symm (Sum.inr i))
  have he : ∀ i, F.free (e i) = a.symm (Sum.inl i) := by
    intro i
    have hh := congrArg Subtype.val (F.directionEquiv.apply_symm_apply (t.symm i))
    exact hh
  refine ⟨e, z, ?_⟩
  intro x
  funext j
  cases hj : a j with
  | inl i =>
    have hji : a.symm (Sum.inl i) = j := by rw [← hj, a.symm_apply_apply]
    have hfree : F.free (e i) = j := (he i).trans hji
    rw [← hfree, F.map_free]
    change x (e i) = Sum.elim (fun i => x (e i)) z (a (F.free (e i)))
    rw [hfree, hj]
    rfl
  | inr i =>
    have hji : a.symm (Sum.inr i) = j := by rw [← hj, a.symm_apply_apply]
    have hfixed : ∀ b, F.free b ≠ j := by
      intro b hb
      obtain ⟨c, rfl⟩ := e.surjective b
      have hh := (he c).symm.trans hb
      have := congrArg a hh
      rw [a.apply_symm_apply, hj] at this
      cases this
    rw [F.map_fixed x j hfixed]
    change F.anchor j = Sum.elim (fun i => x (e i)) z (a j)
    rw [hj]
    exact congrArg F.anchor hji.symm

end LeanProofs.GowersSzemeredi
