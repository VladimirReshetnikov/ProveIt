import GowersSzemeredi.Proofs16FreimanFrequencyTranslation

/-! Refine a coherent family into any dense subset of the common quarter
Bohr set. Whole-quadruple averaging and row labels preserve coherence,
while the varying frequency maps remain unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasCoherentTranslationRefinement {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X Y Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (rho sigma density : Real) : Prop :=
    ∃ (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (V : Finset (ZMod N))
      (R : Finset (Fin 4 → ZMod N)),
      t 0+t 1 = t 2+t 3 ∧ (∀ j, t j ∈ bohr Gamma (rho/2)) ∧ V ⊆ Y ∧
      density*N ≤ (V.card : Real) ∧ density*(N : Real)^3 ≤ R.card ∧
      (∀ u ∈ V, t (color u)+u ∈ X ∧
        IsFreimanLinearOn (freimanFrequencyBohr (translatedFrequencyBase B theta t) theta (sigma/2) u)
          (F (t (color u)+u)) ∧ F (t (color u)+u) 0 = 0) ∧
      ∀ b ∈ R, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ V ∧ color (b j) = j) ∧ (fun j => t j+b j) ∈ Q ∧
        ∀ z, (∀ j, z ∈ freimanFrequencyBohr (translatedFrequencyBase B theta t) theta (sigma/2) (b j)) →
          F (t (color (b 0))+b 0) z+F (t (color (b 1))+b 1) z =
            F (t (color (b 2))+b 2) z+F (t (color (b 3))+b 3) z

theorem coherent_translation_localization {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X Y Gamma B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {rho sigma kappa p : Real} (hrho : 0 ≤ rho) (hk : 0 < kappa) (hp : 0 < p)
    (htheta : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    (hX : X ⊆ bohr Gamma (rho/4)) (hY : Y ⊆ bohr Gamma (rho/4))
    (hlocal : ∀ x ∈ X, IsFreimanLinearOn (freimanFrequencyBohr B theta sigma x) (F x) ∧ F x 0 = 0)
    (hquad : ∀ a ∈ Q, a 0+a 1 = a 2+a 3 ∧ (∀ j, a j ∈ X) ∧
      ∀ z, (∀ j, z ∈ freimanFrequencyBohr B theta sigma (a j)) →
        F (a 0) z+F (a 1) z = F (a 2) z+F (a 3) z)
    (hmass : kappa*(N : Real)^3 ≤ Q.card) (hYmass : p*N ≤ (Y.card : Real))
    (hN : 8 ≤ (kappa*p^4)*(N : Real)) :
    HasCoherentTranslationRefinement Q X Y Gamma B theta F rho sigma (kappa*p^4/512) := by
  obtain ⟨t,ht,hcount⟩ := exists_dense_additive_translation Q Y
    (fun a ha => (hquad a ha).1) hp.le hmass hYmass
  let S := recenteredQuadruples (localizedQuadruples Q Y t) t
  have hS : (kappa*p^4)*(N : Real)^3 ≤ (S.card : Real) := by
    simpa only [S,recenteredQuadruples_card] using hcount
  have hrealize := recentered_localized_quadruples Q Y t (fun a ha => (hquad a ha).1) ht
  have hSne : S.Nonempty := Finset.card_pos.mp (by
    have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    exact_mod_cast (show 0 < kappa*p^4*(N : Real)^3 by positivity).trans_le hS)
  have htmem (j : Fin 4) : t j ∈ bohr Gamma (rho/2) := by
    obtain ⟨b,hb⟩ := hSne
    obtain ⟨hba,hbY,hbQ⟩ := hrealize b hb
    have h := bohr_sub_radius Gamma (hX ((hquad _ hbQ).2.1 j)) (hY (hbY j))
    simpa only [add_sub_cancel_right,show rho/4+rho/4 = rho/2 by ring] using h
  obtain ⟨color,R,hRS,hR,hlabels⟩ := exists_dense_quadruple_row_labels S
    (fun b hb => (hrealize b hb).1) hS hN
  let V := labeledRowSupport S color
  have hsource (u : ZMod N) (hu : u ∈ V) : u ∈ Y ∧ t (color u)+u ∈ X := by
    obtain ⟨b,hb,he⟩ := labeledRowSupport_witness S color hu
    have h := hrealize b hb
    exact ⟨he ▸ h.2.1 (color u),by simpa only [he] using (hquad _ h.2.2).2.1 (color u)⟩
  have hmem (b : Fin 4 → ZMod N) (hb : b ∈ R) (j : Fin 4) : b j ∈ V := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [(hlabels b hb).2 j]
    exact Finset.mem_image.mpr ⟨b,hRS hb,rfl⟩
  have hsub (j : Fin 4) (u : ZMod N) (hu : u ∈ Y) :
      freimanFrequencyBohr (translatedFrequencyBase B theta t) theta (sigma/2) u ⊆
        freimanFrequencyBohr B theta sigma (t j+u) :=
    translated_frequency_bohr_subset B theta t j u
      (freiman_bohr_translation Gamma theta hrho htheta (htmem j) (hY hu))
  refine ⟨t,color,V,R,ht,htmem,fun u hu => (hsource u hu).1,?_,hR,?_,?_⟩
  · have hrow := additive_quadruples_row_density R (fun b hb => (hrealize b (hRS hb)).1) hR 0
    have hsubV : anchorRowSupport R 0 ⊆ V := by
      intro u hu
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hu
      exact hmem b hb 0
    exact hrow.trans (by exact_mod_cast Finset.card_le_card hsubV)
  · intro u hu
    have hs := hsource u hu
    have hl := hlocal _ hs.2
    exact ⟨hs.2,hl.1.mono (hsub (color u) u hs.1),hl.2⟩
  · intro b hb
    have hr := hrealize b (hRS hb)
    refine ⟨hr.1,(hlabels b hb).1,fun j => ⟨hmem b hb j,(hlabels b hb).2 j⟩,hr.2.2,?_⟩
    intro z hz
    simp only [(hlabels b hb).2]
    exact (hquad _ hr.2.2).2.2 z (fun j => hsub j (b j) (hr.2.1 j) (hz j))

end LeanProofs.GowersSzemeredi
