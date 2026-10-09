import GowersSzemeredi.Proofs16CoherentNestedAccuracy

/-! Two compatible-word layers share the same maps and frequency system.
The second layer's ambient set lies in the first layer's anchor set. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasCoherentNestedWordFamily {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma kappa : Real) (K L : Nat) : Prop :=
  let T := fun u => B ∪ Finset.univ.image (fun j => theta j u)
  ∃ A P : Finset (ZMod N), A ⊆ X ∧ P ⊆ A ∧
    (9*kappa^2/512)*N ≤ (A.card : Real) ∧ (9*kappa^2/1024)*N ≤ (P.card : Real) ∧
    ThresholdColumnRichness A T F (sigma/1296) (coherentWordDensity kappa K/2) (coherentRobustWalkDensity kappa) ∧
    (∀ a ∈ P, coherentAnchorTripleDensity kappa*(N : Real)^2 ≤
      (columnTripleRepresentations A T F (sigma/1296) a).card) ∧
    (∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ P) → as.length ≤ K →
      coherentWordDensity kappa as.length*(N : Real)^(3*as.length+2) ≤
        (columnWordRepresentations A T F (sigma/1296) (a::as)).card) ∧
    coherentNestedDensity kappa*(N : Real)^3 ≤ (exactColumnQuadruples P T F (sigma/1296)).card ∧
    HasCoherentWordFamily P B theta F (sigma/1296) (coherentNestedDensity kappa) L

theorem CoherentBridgeSystem.nested_word_family {N ell depth : Nat} [NeZero N] [Fact N.Prime]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real} {Q : Finset (Fin 4 → ZMod N)} (K L : Nat)
    (h : CoherentBridgeSystem B X theta F sigma
      (kappa^(coherentNestedBridgePower K L)/coherentNestedBridgeScale K L) depth)
    (hs : 0 ≤ sigma) (hdepth : 7 ≤ depth) (hfamily : CoherentFrequencyFamily X B theta F sigma Q)
    (hk : 0 < kappa) (hmass : kappa*(N : Real)^3 ≤ Q.card) (hN : 2 < N) :
    HasCoherentNestedWordFamily X B theta F sigma kappa K L := by
  have hk1 := hfamily.density_le_one hmass
  obtain ⟨A,P,hAX,hPA,hA,hP,hrich,htrip,hwords⟩ :=
    h.word_family_of_le K (coherentNestedBridgeAccuracy_first hk.le hk1 K L)
      (by omega) hfamily hk hmass hN
  have hquad := hrich.anchor_quadruples hk hk1 hPA hP
  have hnew := hfamily.exact_subfamily (hPA.trans hAX) (by linarith : sigma/1296 ≤ sigma)
  have hshift := (h.restrict (hPA.trans hAX)).shift 4 (d := 3) (by omega)
  norm_num only [show (6 : Real)^4=1296 by norm_num] at hshift
  have hsecond := hshift.word_family_of_le L (coherentNestedBridgeAccuracy_second hk.le hk1 K L)
    le_rfl hnew (coherentNestedDensity_pos hk) hquad hN
  exact ⟨A,P,hAX,hPA,hA,hP,hrich,htrip,hwords,hquad,hsecond⟩

end LeanProofs.GowersSzemeredi
