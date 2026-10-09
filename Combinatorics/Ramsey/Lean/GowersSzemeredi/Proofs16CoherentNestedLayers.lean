import GowersSzemeredi.Proofs16CoherentNestedWordFamily
import GowersSzemeredi.Proofs16CoherentNestedEndpointScale

/-! Unpack both dense layers with their actual endpoint identities on a
single profile radius, ready for the common-extension argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem HasCoherentNestedWordFamily.layers {N ell K J : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real}
    (h : HasCoherentNestedWordFamily X B theta F sigma kappa K J)
    (hs : 0 ≤ sigma) (houter : CoherentWordEndpointIdentities X B theta F sigma)
    (hinner : CoherentWordEndpointIdentities X B theta F (sigma/1296)) :
    let T := fun u => B ∪ Finset.univ.image (fun j => theta j u)
    let r := coherentNestedProfileRadius sigma K J
    ∃ A P C D : Finset (ZMod N), A ⊆ X ∧ P ⊆ A ∧ C ⊆ P ∧ D ⊆ C ∧
      (9*kappa^2/512)*N ≤ (A.card : Real) ∧ (9*kappa^2/1024)*N ≤ (P.card : Real) ∧
      (9*(coherentNestedDensity kappa)^2/512)*N ≤ (C.card : Real) ∧
      (9*(coherentNestedDensity kappa)^2/1024)*N ≤ (D.card : Real) ∧
      (∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ P) → as.length ≤ K →
        coherentWordDensity kappa as.length*(N : Real)^(3*as.length+2) ≤
          (columnWordRepresentations A T F (sigma/1296) (a::as)).card ∧
        ∀ w ∈ columnWordRepresentations A T F (sigma/1296) (a::as), ColumnWordIdentity T F r (a::as) w) ∧
      (∀ (a : ZMod N) (as : List (ZMod N)), (∀ x ∈ a::as, x ∈ D) → as.length ≤ J →
        coherentWordDensity (coherentNestedDensity kappa) as.length*(N : Real)^(3*as.length+2) ≤
          (columnWordRepresentations C T F ((sigma/1296)/1296) (a::as)).card ∧
        ∀ w ∈ columnWordRepresentations C T F ((sigma/1296)/1296) (a::as),
          ColumnWordIdentity T F r (a::as) w ∧ (∀ x ∈ columnWordEntries w, x ∈ P)) := by
  obtain ⟨A,P,hAX,hPA,hA,hP,hrich,htrip,hwords,hquad,hsecond⟩ := h
  obtain ⟨C,D,hCP,hDC,hC,hD,hrich2,htrip2,hwords2⟩ := hsecond
  refine ⟨A,P,C,D,hAX,hPA,hCP,hDC,hA,hP,hC,hD,?_,?_⟩
  · intro a as has hlen
    refine ⟨hwords a as has hlen,?_⟩
    intro w hw
    exact houter.at_nested_scale hs K J hAX (a::as) w (by simp only [List.length_cons]; omega) hw
  · intro a as has hlen
    refine ⟨hwords2 a as has hlen,?_⟩
    intro w hw
    refine ⟨(hinner C (hCP.trans (hPA.trans hAX)) (a::as) w hw).mono_radius
      (coherentNestedProfileRadius_le_inner hs K J (a::as).length (by simp only [List.length_cons]; omega)),?_⟩
    intro x hx
    exact hCP (columnWordEntries_mem C w (columnWordRepresentations_spec C _ F _ _ w hw).1 x hx)

end LeanProofs.GowersSzemeredi
