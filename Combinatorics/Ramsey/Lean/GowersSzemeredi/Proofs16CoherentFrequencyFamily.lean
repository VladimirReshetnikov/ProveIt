import GowersSzemeredi.Proofs16SourceTranslationOffsets

/-! Coherent frequency families and their source maps. Source maps retain
both original points and whole original configurations through refinement. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def CoherentFrequencyFamily {N ell : Nat} [NeZero N] (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (sigma : Real) (Q : Finset (Fin 4 → ZMod N)) : Prop :=
  (∀ x ∈ X, IsFreimanLinearOn (freimanFrequencyBohr B theta sigma x) (F x) ∧ F x 0 = 0) ∧
  ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ (∀ j, a j ∈ X) ∧
    ∀ z, (∀ j, z ∈ freimanFrequencyBohr B theta sigma (a j)) →
      F (a 0) z+F (a 1) z = F (a 2) z+F (a 3) z

theorem CoherentFrequencyFamily.mono_radius {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma tau : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentFrequencyFamily X B theta F sigma Q) (ht : tau ≤ sigma) :
    CoherentFrequencyFamily X B theta F tau Q := by
  refine ⟨fun x hx => ⟨(h.1 x hx).1.mono (bohr_mono_radius _ ht),(h.1 x hx).2⟩,?_⟩
  intro a ha
  refine ⟨(h.2 a ha).1,(h.2 a ha).2.1,?_⟩
  intro z hz
  exact (h.2 a ha).2.2 z (fun j => bohr_mono_radius _ ht (hz j))

theorem CoherentFrequencyFamily.point_density {N ell : Nat} [NeZero N]
    {X B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma kappa : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentFrequencyFamily X B theta F sigma Q) (hmass : kappa*(N : Real)^3 ≤ Q.card) :
    kappa*N ≤ (X.card : Real) := by
  have hp := additive_quadruples_row_density Q (fun a ha => (h.2 a ha).1) hmass 0
  have hsub : anchorRowSupport Q 0 ⊆ X := by
    intro u hu
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
    exact (h.2 a ha).2.1 0
  exact hp.trans (by exact_mod_cast Finset.card_le_card hsub)

theorem HasCoherentTranslationRefinement.frequency_family {N ell : Nat} [NeZero N]
    {Q : Finset (Fin 4 → ZMod N)} {X Y Gamma B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {F : ZMod N → ZMod N → ZMod N}
    {rho sigma density : Real}
    (h : HasCoherentTranslationRefinement Q X Y Gamma B theta F rho sigma density) :
    ∃ (B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
      B ⊆ B' ∧ B'.card ≤ B.card+4*ell ∧ V ⊆ Y ∧
      density*N ≤ (V.card : Real) ∧ density*(N : Real)^3 ≤ R.card ∧
      (sourceTranslationOffsets source).card ≤ 4 ∧
      (∀ u ∈ V, source u ∈ X) ∧ (∀ b ∈ R, (fun j => source (b j)) ∈ Q) ∧
      CoherentFrequencyFamily V B' theta (fun u => F (source u)) (sigma/2) R := by
  obtain ⟨t,color,V,R,ht,htmem,hV,hVmass,hRmass,hlocal,hquad⟩ := h
  let source := fun u => t (color u)+u
  refine ⟨translatedFrequencyBase B theta t,V,R,source,Finset.subset_union_left,
    translatedFrequencyBase_card_le B theta t,hV,hVmass,hRmass,sourceTranslationOffsets_row_card_le t color,fun u hu => (hlocal u hu).1,?_,?_,?_⟩
  · intro b hb
    have he : (fun j => source (b j)) = fun j => t j+b j := by
      funext j
      dsimp only [source]
      rw [((hquad b hb).2.2.1 j).2]
    rw [he]
    exact (hquad b hb).2.2.2.1
  · intro u hu
    exact (hlocal u hu).2
  · intro b hb
    exact ⟨(hquad b hb).1,fun j => ((hquad b hb).2.2.1 j).1,(hquad b hb).2.2.2.2⟩

end LeanProofs.GowersSzemeredi
