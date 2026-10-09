import GowersSzemeredi.Proofs16HigherArrangementFirstPairMap
import GowersSzemeredi.Proofs16HigherArrangementCoordinateSymmetry

/-! Even-coordinate symmetries preserve the order of each endpoint pair,
so the common difference map is available for any of the eight pairs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementPairLeft (j : Fin 8) : Fin 16 := ⟨2*j.val,by omega⟩
def higherArrangementPairRight (j : Fin 8) : Fin 16 := ⟨2*j.val+1,by omega⟩
def higherArrangementPairDifference {N : Nat} (p : HigherArrangementParameter N) (j : Fin 8) : ZMod N :=
  higherArrangementEndpoints p (higherArrangementPairLeft j)-
    higherArrangementEndpoints p (higherArrangementPairRight j)

theorem higherArrangementPairDifference_additive {N : Nat} (p : HigherArrangementParameter N) :
    higherArrangementPairDifference p 0+higherArrangementPairDifference p 1 =
      higherArrangementPairDifference p 2+higherArrangementPairDifference p 3 := by
  dsimp [higherArrangementPairDifference,higherArrangementPairLeft,higherArrangementPairRight,
    higherArrangementEndpoints]
  ring

theorem higherArrangementPairDifference_sides {N : Nat} (p : HigherArrangementParameter N) (j : Fin 4) :
    higherArrangementPairDifference p (Fin.castAdd 4 j) =
      higherArrangementPairDifference p (Fin.natAdd 4 j) := by
  fin_cases j <;> dsimp [higherArrangementPairDifference,higherArrangementPairLeft,
    higherArrangementPairRight,higherArrangementEndpoints] <;> ring

theorem higherArrangementCoordinateSymmetry_pair_right (N : Nat) (j : Fin 8) :
    (higherArrangementCoordinateSymmetry N (higherArrangementPairLeft j)).coordinates 1 =
      higherArrangementPairRight j := by
  fin_cases j <;> rfl

theorem higher_arrangements_pair_frequency_map {N : Nat} [NeZero N]
    (f : Fin 16 → ZMod N → ZMod N) (E : Fin 16 → Finset (ZMod N))
    (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    (hE : ∀ i, FreimanHom 8 (E i) (f i))
    (hcoord : ∀ p ∈ Q, ∀ i, higherArrangementEndpoints p i ∈ E i)
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) (j : Fin 8) :
    ∃ (theta : PairFrequencyMap N) (R : Finset (HigherArrangementParameter N)),
      theta.Controlled (delta^2) ∧ R ⊆ Q ∧
      offsetDifferenceProgressionRetention delta*(N : Real)^11 ≤ R.card ∧
      ∀ p ∈ R, higherArrangementPairDifference p j ∈ theta.domain ∧
        theta.toFun (higherArrangementPairDifference p j) =
          f (higherArrangementPairLeft j) (higherArrangementEndpoints p (higherArrangementPairLeft j))-
          f (higherArrangementPairRight j) (higherArrangementEndpoints p (higherArrangementPairRight j)) := by
  let s := higherArrangementCoordinateSymmetry N (higherArrangementPairLeft j)
  let Q' := Q.image s.parameters
  let g := fun i => f (s.coordinates i)
  have hQ' : ∀ p ∈ Q', HigherArrangementEquation g p := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    exact s.equation f q (hQ q hq)
  have hcoords : ∀ p ∈ Q', ∀ i, higherArrangementEndpoints p i ∈ E (s.coordinates i) := by
    intro p hp i
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    rw [s.endpoints]
    exact hcoord q hq _
  have hcount' : delta*(N : Real)^11 ≤ Q'.card := by
    simpa only [Q',Finset.card_image_of_injective _ s.parameters.injective] using hcount
  obtain ⟨theta,R',hcontrol,hR'Q',hR',hvalue⟩ := higher_arrangements_first_pair_frequency_map g Q'
    (E (s.coordinates 0)) (E (s.coordinates 1)) hQ' (fun p hp => hcoords p hp 0)
    (fun p hp => hcoords p hp 1) (hE _) (hE _) hd hcount'
  let R := R'.image s.parameters.symm
  have hRcard : R.card = R'.card := Finset.card_image_of_injective _ s.parameters.symm.injective
  have hRsub : R ⊆ Q := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨r,hr,hrq⟩ := Finset.mem_image.mp (hR'Q' hq)
    rw [← hrq,s.parameters.symm_apply_apply]
    exact hr
  have hdifference (p : HigherArrangementParameter N) :
      higherArrangementPairDifference p j = (s.parameters p).1.1 := by
    have h0 := s.endpoints p 0
    have h1 := s.endpoints p 1
    simp only [s,higherArrangementCoordinateSymmetry_zero,higherArrangementCoordinateSymmetry_pair_right] at h0 h1
    change (s.parameters p).2+(s.parameters p).1.1 =
      higherArrangementEndpoints p (higherArrangementPairLeft j) at h0
    change (s.parameters p).2 = higherArrangementEndpoints p (higherArrangementPairRight j) at h1
    dsimp [higherArrangementPairDifference]
    linear_combination -h0+h1
  refine ⟨theta,R,hcontrol,hRsub,by simpa only [hRcard] using hR',?_⟩
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have h0 := s.endpoints (s.parameters.symm q) 0
  have h1 := s.endpoints (s.parameters.symm q) 1
  simp only [Equiv.apply_symm_apply,s,higherArrangementCoordinateSymmetry_zero,
    higherArrangementCoordinateSymmetry_pair_right] at h0 h1
  rw [hdifference,Equiv.apply_symm_apply]
  refine ⟨(hvalue q hq).1,?_⟩
  have hv := (hvalue q hq).2
  simpa only [g,s,higherArrangementCoordinateSymmetry_zero,higherArrangementCoordinateSymmetry_pair_right,
    h0,h1] using hv

end LeanProofs.GowersSzemeredi
