import GowersSzemeredi.Proofs16HigherArrangementCoordinateSymmetry
import GowersSzemeredi.Proofs16HigherArrangementFirstExtraction

/-! Bijective symmetries transfer first-coordinate extraction to any
endpoint with the same density loss and the original family retained. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem higher_arrangements_retain_coordinate {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 16 → ZMod N → ZMod N) (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) (i : Fin 16) :
    ∃ (E : Finset (ZMod N)) (R : Finset (HigherArrangementParameter N)),
      E ⊆ Q.image (fun p => higherArrangementEndpoints p i) ∧ R ⊆ Q ∧
      (∀ p ∈ R, higherArrangementEndpoints p i ∈ E) ∧ FreimanHom 8 E (f i) ∧
      (2 : Real)^(-(1882 : Real))*(((delta/2)^2)^4)^1164*N ≤ E.card ∧
      offsetFreimanRetention delta*(N : Real)^11 ≤ R.card := by
  let s := higherArrangementCoordinateSymmetry N i
  let Q' := Q.image s.parameters
  let g := fun j => f (s.coordinates j)
  have hQ' : ∀ p ∈ Q', HigherArrangementEquation g p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact s.equation f q (hQ q hq)
  have hcount' : delta*(N : Real)^11 ≤ Q'.card := by
    simpa only [Q',Finset.card_image_of_injective _ s.parameters.injective] using hcount
  obtain ⟨E,R',hEQ',hR'Q',hcoord,hF,hE,hR'⟩ :=
    higher_arrangements_retain_first_freiman_piece g Q' hQ' hd hcount'
  let R := R'.image s.parameters.symm
  have hRcard : R.card = R'.card := Finset.card_image_of_injective _ s.parameters.symm.injective
  have hEsub : E ⊆ Q.image (fun p => higherArrangementEndpoints p i) := by
    intro x hx
    obtain ⟨p,hp,hpx⟩ := Finset.mem_image.mp (hEQ' hx)
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_image.mpr ⟨q,hq,by
      simpa only [s.endpoints,s,higherArrangementCoordinateSymmetry_zero] using hpx⟩
  have hRsub : R ⊆ Q := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨r,hr,hrq⟩ := Finset.mem_image.mp (hR'Q' hq)
    rw [← hrq,s.parameters.symm_apply_apply]
    exact hr
  refine ⟨E,R,hEsub,hRsub,?_,?_,hE,?_⟩
  · intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    have he := s.endpoints (s.parameters.symm q) 0
    simp only [Equiv.apply_symm_apply,s,higherArrangementCoordinateSymmetry_zero] at he
    rw [← he]
    exact hcoord q hq
  · simpa only [g,s,higherArrangementCoordinateSymmetry_zero] using hF
  · simpa only [hRcard] using hR'

end LeanProofs.GowersSzemeredi
