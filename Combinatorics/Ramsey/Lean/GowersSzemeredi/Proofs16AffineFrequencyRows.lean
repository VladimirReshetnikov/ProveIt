import GowersSzemeredi.Proofs16AdditiveProperProgressionLocalization
import GowersSzemeredi.Proofs16CommonProgressionDomain

/-! Common difference extensions turn the original frequency values
into affine formulas on the retained portions of four progression translates.
The translation centers need not belong to the original row supports. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem frequency_rows_affine_on_progression {N m : Nat} [NeZero N]
    (R S : Finset (Fin 4 → ZMod N)) (Gamma : Finset (ZMod N))
    (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (t : Fin 4 → ZMod N)
    (J : Fin 4 → Finset (Fin m)) (f psi : Fin 4 → Fin m → ZMod N → ZMod N) {rho : Real}
    (hr : 0 ≤ rho) (hP : P.carrier ⊆ bohr Gamma (rho/4)) (hS : S.Nonempty)
    (hSP : ∀ b ∈ S, ∀ j, b j ∈ P.carrier) (hSR : ∀ b ∈ S, (fun j => t j+b j) ∈ R)
    (hpsi : ∀ j, ∀ i ∈ J j, FreimanHom 2 (bohr Gamma rho) (psi j i) ∧ psi j i 0 = 0 ∧
      ∀ x ∈ anchorRowSupport R j, ∀ y ∈ anchorRowSupport R j,
        x-y ∈ bohr Gamma rho → f j i x-f j i y = psi j i (x-y)) :
    ∃ c : Fin 4 → Fin m → ZMod N,
      ∀ j, ∀ i ∈ J j, ∀ x ∈ anchorRowSupport S j, f j i (t j+x) = c j i+psi j i x := by
  have hW (j : Fin 4) : anchorRowSupport S j ⊆ P.carrier := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact hSP b hb j
  have hdom (j : Fin 4) : ∀ x ∈ anchorRowSupport S j, t j+x+0 ∈ anchorRowSupport R j := by
    intro x hx
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨fun j => t j+b j,hSR b hb,by simp⟩
  have hex (j : Fin 4) (i : Fin m) : ∃ c : ZMod N,
      i ∈ J j → ∀ x ∈ anchorRowSupport S j, f j i (t j+x) = c+psi j i x := by
    by_cases hi : i ∈ J j
    · obtain ⟨c,hc⟩ := affine_on_progression_cluster (anchorRowSupport R j) Gamma
        (anchorRowSupport S j) P (f j i) (psi j i) (t j) 0 hr hP (hW j) (hS.image _)
        (hpsi j i hi).1 (hpsi j i hi).2.1 (hpsi j i hi).2.2 (hdom j)
      exact ⟨c,fun _ x hx => by simpa only [add_zero] using hc x hx⟩
    · exact ⟨0,fun h => (hi h).elim⟩
  choose c hc using hex
  exact ⟨c,hc⟩

end LeanProofs.GowersSzemeredi
