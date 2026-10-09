import GowersSzemeredi.Proofs16HigherArrangementPairMap

/-! Successive pair alignment retains one family of original higher
arrangements. Each chosen progression map has controls at an explicitly
recorded stage of the density iteration. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherArrangementPairDensity (delta : Real) : Nat → Real
  | 0 => delta
  | n+1 => offsetDifferenceProgressionRetention (higherArrangementPairDensity delta n)

def higherArrangementPairValue {N : Nat} (f : Fin 16 → ZMod N → ZMod N)
    (p : HigherArrangementParameter N) (j : Fin 8) : ZMod N :=
  f (higherArrangementPairLeft j) (higherArrangementEndpoints p (higherArrangementPairLeft j))-
    f (higherArrangementPairRight j) (higherArrangementEndpoints p (higherArrangementPairRight j))

theorem higherArrangementPairDensity_pos {delta : Real} (hd : 0 < delta) (n : Nat) :
    0 < higherArrangementPairDensity delta n := by
  induction n with
  | zero => exact hd
  | succ n ih => exact offsetDifferenceProgressionRetention_pos ih

theorem higher_arrangements_retain_pair_maps {N : Nat} [NeZero N]
    (f : Fin 16 → ZMod N → ZMod N) (E : Fin 16 → Finset (ZMod N))
    (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    (hE : ∀ i, FreimanHom 8 (E i) (f i))
    (hcoord : ∀ p ∈ Q, ∀ i, higherArrangementEndpoints p i ∈ E i)
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card)
    (S : Finset (Fin 8)) :
    ∃ (theta : Fin 8 → PairFrequencyMap N) (R : Finset (HigherArrangementParameter N)),
      R ⊆ Q ∧
      (∀ j ∈ S, ∃ n < S.card, (theta j).Controlled ((higherArrangementPairDensity delta n)^2)) ∧
      (∀ p ∈ R, ∀ j ∈ S, higherArrangementPairDifference p j ∈ (theta j).domain ∧
        (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j) ∧
      higherArrangementPairDensity delta S.card*(N : Real)^11 ≤ R.card := by
  induction S using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => ⟨⟨0,Fin.elim0,Fin.elim0⟩,0,fun _ => 0⟩,Q,
      Finset.Subset.refl _,by simp,by simp,hcount⟩
  | @insert j S hj ih =>
    obtain ⟨theta,R,hRQ,hcontrol,hvalue,hR⟩ := ih
    obtain ⟨g,R',hg,hR'R,hR',hnew⟩ := higher_arrangements_pair_frequency_map f E R
      (fun p hp => hQ p (hRQ hp)) hE (fun p hp => hcoord p (hRQ hp))
      (higherArrangementPairDensity_pos hd S.card) hR j
    refine ⟨Function.update theta j g,R',hR'R.trans hRQ,?_,?_,?_⟩
    · intro i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simp only [Function.update_self,Finset.card_insert_of_notMem hj]
        exact ⟨S.card,Nat.lt_succ_self _,hg⟩
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        obtain ⟨n,hn,hncontrol⟩ := hcontrol i hi
        simp only [Function.update_of_ne hij,Finset.card_insert_of_notMem hj]
        exact ⟨n,Nat.lt_succ_of_lt hn,hncontrol⟩
    · intro p hp i hi
      rcases Finset.mem_insert.mp hi with rfl | hi
      · simpa only [Function.update_self,higherArrangementPairValue] using hnew p hp
      · have hij : i ≠ j := fun h => hj (h ▸ hi)
        simpa only [Function.update_of_ne hij] using hvalue p (hR'R hp) i hi
    · simpa only [Finset.card_insert_of_notMem hj,higherArrangementPairDensity] using hR'

/-- Eight translated progression maps represent all paired differences
on the same dense family of original arrangements. -/
theorem higher_arrangements_pair_map_family {N : Nat} [NeZero N]
    (f : Fin 16 → ZMod N → ZMod N) (E : Fin 16 → Finset (ZMod N))
    (Q : Finset (HigherArrangementParameter N))
    (hQ : ∀ p ∈ Q, HigherArrangementEquation f p)
    (hE : ∀ i, FreimanHom 8 (E i) (f i))
    (hcoord : ∀ p ∈ Q, ∀ i, higherArrangementEndpoints p i ∈ E i)
    {delta : Real} (hd : 0 < delta) (hcount : delta*(N : Real)^11 ≤ Q.card) :
    ∃ (theta : Fin 8 → PairFrequencyMap N) (R : Finset (HigherArrangementParameter N)),
      R ⊆ Q ∧
      (∀ j, ∃ n < 8, (theta j).Controlled ((higherArrangementPairDensity delta n)^2)) ∧
      (∀ p ∈ R, ∀ j, higherArrangementPairDifference p j ∈ (theta j).domain ∧
        (theta j).toFun (higherArrangementPairDifference p j) = higherArrangementPairValue f p j) ∧
      higherArrangementPairDensity delta 8*(N : Real)^11 ≤ R.card := by
  obtain ⟨theta,R,hRQ,hcontrol,hvalue,hR⟩ :=
    higher_arrangements_retain_pair_maps f E Q hQ hE hcoord hd hcount Finset.univ
  refine ⟨theta,R,hRQ,?_,fun p hp j => hvalue p hp j (Finset.mem_univ _),?_⟩
  · intro j
    simpa only [Finset.card_univ,Fintype.card_fin] using hcontrol j (Finset.mem_univ _)
  · simpa only [Finset.card_univ,Fintype.card_fin] using hR

end LeanProofs.GowersSzemeredi
