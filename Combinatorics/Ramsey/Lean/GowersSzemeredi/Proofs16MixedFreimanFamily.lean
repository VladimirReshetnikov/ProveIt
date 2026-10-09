import GowersSzemeredi.Proofs16MixedCoordinateDensity

/-! Successive coordinate extraction preserves a dense family on which
all four selected maps have order-eight Freiman structure. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedConfigurationDensity (delta : Real) : Nat → Real
  | 0 => delta
  | n+1 => mixedConfigurationRetention (mixedConfigurationDensity delta n)

theorem mixedConfigurationDensity_pos {delta : Real} (hdelta : 0 < delta) (n : Nat) :
    0 < mixedConfigurationDensity delta n := by
  induction n with
  | zero => exact hdelta
  | succ n ih => exact mixedConfigurationRetention_pos ih

/-- Preserve all previously extracted coordinates when treating another
one, by restricting only the original configuration family. -/
theorem mixed_configurations_retain_coordinates {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 4 → ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card)
    (S : Finset (Fin 4)) :
    ∃ (E : Fin 4 → Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)),
      R ⊆ Q ∧ (∀ i ∈ S, E i ⊆ Q.image (fun q => q i) ∧ FreimanHom 8 (E i) (f i)) ∧
      (∀ q ∈ R, ∀ i ∈ S, q i ∈ E i) ∧
      mixedConfigurationDensity delta S.card*(N : Real)^3 ≤ R.card := by
  induction S using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅,Q,Finset.Subset.refl _,by simp,by simp,hcount⟩
  | @insert i S hi ih =>
    obtain ⟨E,R,hRQ,hE,hcoords,hR⟩ := ih
    obtain ⟨D,R',hDR,hR'R,hDcoords,hDF,_,hR'⟩ := mixed_configurations_retain_coordinate f R
      (hRQ.trans hQ) (mixedConfigurationDensity_pos hdelta S.card) hR i
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
    · simpa only [Finset.card_insert_of_notMem hi,mixedConfigurationDensity] using hR'

/-- All four maps become Freiman on their respective coordinate sets,
while an explicitly dense subfamily of the original configurations remains. -/
theorem mixed_configurations_freiman_family {N : Nat} [NeZero N] [Fact N.Prime]
    (f : Fin 4 → ZMod N → ZMod N) (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ (E : Fin 4 → Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)),
      R ⊆ Q ∧ (∀ i, E i ⊆ Q.image (fun q => q i) ∧ FreimanHom 8 (E i) (f i)) ∧
      (∀ i, mixedConfigurationDensity delta 4*N ≤ ((E i).card : Real)) ∧
      (∀ q ∈ R, ∀ i, q i ∈ E i) ∧
      mixedConfigurationDensity delta 4*(N : Real)^3 ≤ R.card := by
  obtain ⟨E,R,hRQ,hE,hcoord,hR⟩ := mixed_configurations_retain_coordinates f Q hQ hdelta hcount Finset.univ
  have hR' : mixedConfigurationDensity delta 4*(N : Real)^3 ≤ R.card := by
    simpa only [Finset.card_univ,Fintype.card_fin] using hR
  refine ⟨E,R,hRQ,fun i => hE i (Finset.mem_univ _),?_,
    fun q hq i => hcoord q hq i (Finset.mem_univ _),hR'⟩
  intro i
  exact additive_quadruples_coordinate_density R (E i) i
    (fun q hq => (Finset.mem_filter.mp (hQ (hRQ hq))).2.2.1)
    (fun q hq => hcoord q hq i (Finset.mem_univ _)) hR' 

end LeanProofs.GowersSzemeredi
