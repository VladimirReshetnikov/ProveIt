import GowersSzemeredi.Proofs16SharedFreimanBohrSpectrum

/-! All selected frequency maps on the four dense row supports have
normalized difference extensions on one Bohr set. Its rank costs four
spectra, independent of the number of maps selected in each row. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem four_row_common_frequency_bohr {N m : Nat} [NeZero N]
    (E : Fin 4 → Finset (ZMod N)) (J : Fin 4 → Finset (Fin m))
    (f : Fin 4 → Fin m → ZMod N → ZMod N) {kappa : Real} (hk : 0 < kappa)
    (hE : ∀ j, kappa*N ≤ ((E j).card : Real))
    (hf : ∀ j, ∀ i ∈ J j, FreimanHom 8 (E j) (f j i)) :
    ∃ (Gamma : Finset (ZMod N)) (psi : Fin 4 → Fin m → ZMod N → ZMod N),
      (Gamma.card : Real) ≤ 64*kappa^(-(2 : Real)) ∧
      ∀ j, ∀ i ∈ J j, FreimanHom 2 (bohr Gamma (1/(8*Real.pi))) (psi j i) ∧ psi j i 0 = 0 ∧
        ∀ x ∈ E j, ∀ y ∈ E j, x-y ∈ bohr Gamma (1/(8*Real.pi)) →
          f j i x-f j i y = psi j i (x-y) := by
  choose S hS hB using fun j => dense_eight_shared_bohr_spectrum (E j) hk (hE j)
  let Gamma := Finset.univ.biUnion S
  have hG : (Gamma.card : Real) ≤ 64*kappa^(-(2 : Real)) := by
    calc (Gamma.card : Real) ≤ ∑ j : Fin 4, ((S j).card : Real) := by
           exact_mod_cast (Finset.card_biUnion_le (s := (Finset.univ : Finset (Fin 4))) (t := S))
      _ ≤ ∑ _j : Fin 4, 16*kappa^(-(2 : Real)) := Finset.sum_le_sum fun j _ => hS j
      _ = _ := by simp; ring
  have hdom (j : Fin 4) : bohr Gamma (1/(8*Real.pi)) ⊆ bohr (S j) (1/(8*Real.pi)) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun z hz => ?_⟩
    exact (Finset.mem_filter.mp hx).2 z (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hz⟩)
  have hne (j : Fin 4) : (E j).Nonempty := by
    have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    apply Finset.card_pos.mp
    exact_mod_cast (mul_pos hk hn).trans_le (hE j)
  have hex (j : Fin 4) (i : Fin m) : ∃ p : ZMod N → ZMod N,
      i ∈ J j → FreimanHom 2 (bohr Gamma (1/(8*Real.pi))) p ∧ p 0 = 0 ∧
        ∀ x ∈ E j, ∀ y ∈ E j, x-y ∈ bohr Gamma (1/(8*Real.pi)) → f j i x-f j i y = p (x-y) := by
    by_cases hi : i ∈ J j
    · have hb := (hB j (f j i) (hf j i hi)).mono_neighborhood (hdom j)
      obtain ⟨p,hp,hp0,_,hagrees⟩ := hb.normalized_extension (hne j) (zero_mem_bohr Gamma (by positivity))
      exact ⟨p,fun _ => ⟨hp,hp0,hagrees⟩⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose psi hpsi using hex
  exact ⟨Gamma,psi,hG,hpsi⟩

end LeanProofs.GowersSzemeredi
