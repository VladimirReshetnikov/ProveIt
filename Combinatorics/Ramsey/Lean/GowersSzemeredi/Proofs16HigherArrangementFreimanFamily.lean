import GowersSzemeredi.Proofs16HigherArrangementCoordinateDensity

/-! Successive coordinate extraction preserves a dense family on which
all sixteen selected maps have order-eight Freiman structure. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementDensity (delta : Real) : Nat → Real
  | 0 => delta
  | n+1 => offsetFreimanRetention (higherArrangementDensity delta n)

theorem higherArrangementDensity_pos {delta : Real} (hdelta : 0 < delta) (n : Nat) :
    0 < higherArrangementDensity delta n := by
  induction n with
  | zero => exact hdelta
  | succ n ih => exact offsetFreimanRetention_pos ih

/-- Preserve all previously extracted coordinates when treating another
one, by restricting only the original configuration family. -/
theorem higher_arrangements_retain_coordinates {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 16 → ZMod N → ZMod N) (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card)
    (S : Finset (Fin 16)) :
    ∃ (E : Fin 16 → Finset (ZMod N)) (R : Finset (HigherArrangementParameter N)),
      R ⊆ Q ∧ (∀ i ∈ S, E i ⊆ Q.image (fun q => higherArrangementEndpoints q i) ∧ FreimanHom 8 (E i) (f i)) ∧
      (∀ q ∈ R, ∀ i ∈ S, higherArrangementEndpoints q i ∈ E i) ∧
      higherArrangementDensity delta S.card*(N : Real)^11 ≤ R.card := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅,Q,Finset.Subset.refl _,by simp,by simp,hcount⟩
  | @insert i S hi ih =>
    obtain ⟨E,R,hRQ,hE,hcoords,hR⟩ := ih
    obtain ⟨D,R',hDR,hR'R,hDcoords,hDF,_,hR'⟩ := higher_arrangements_retain_coordinate f R
      (fun p hp => hQ p (hRQ hp)) (higherArrangementDensity_pos hdelta S.card) hR i
    refine ⟨Function.update E i D,R',hR'R.trans hRQ,?_,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp only [Function.update_self]
        exact ⟨hDR.trans (Finset.image_subset_image hRQ),hDF⟩
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [Function.update_of_ne hji] using hE j hj
    · intro q hq j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simpa only [Function.update_self] using hDcoords q hq
      · have hji : j ≠ i := fun h => hi (h ▸ hj)
        simpa only [Function.update_of_ne hji] using hcoords q (hR'R hq) j hj
    · simpa only [Finset.card_insert_of_notMem hi,higherArrangementDensity] using hR'

/-- All sixteen maps become Freiman on their respective coordinate sets,
while an explicitly dense subfamily of the original configurations remains. -/
theorem higher_arrangements_freiman_family {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 16 → ZMod N → ZMod N) (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) :
    ∃ (E : Fin 16 → Finset (ZMod N)) (R : Finset (HigherArrangementParameter N)),
      R ⊆ Q ∧ (∀ i, E i ⊆ Q.image (fun q => higherArrangementEndpoints q i) ∧ FreimanHom 8 (E i) (f i)) ∧
      (∀ i, higherArrangementDensity delta 16*N ≤ ((E i).card : Real)) ∧
      (∀ q ∈ R, ∀ i, higherArrangementEndpoints q i ∈ E i) ∧
      higherArrangementDensity delta 16*(N : Real)^11 ≤ R.card := by
  obtain ⟨E,R,hRQ,hE,hcoord,hR⟩ := higher_arrangements_retain_coordinates f Q hQ hdelta hcount Finset.univ
  have hR' : higherArrangementDensity delta 16*(N : Real)^11 ≤ R.card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using hR
  refine ⟨E,R,hRQ,fun i => hE i (Finset.mem_univ _),?_,
    fun q hq i => hcoord q hq i (Finset.mem_univ _),hR'⟩
  intro i
  exact higher_arrangements_coordinate_density R (E i) i
    (fun q hq => hcoord q hq i (Finset.mem_univ _)) hR'

end LeanProofs.GowersSzemeredi
