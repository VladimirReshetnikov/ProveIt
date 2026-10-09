import GowersSzemeredi.Proofs16GlobalSingleProgression
import GowersSzemeredi.Proofs16BohrFourTerm

/-! Translating within the common frequency Bohr set keeps the same
varying maps. Only their values at the four translation centres become
additional fixed frequencies. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def translatedFrequencyBase {N ell : Nat} (B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (t : Fin 4 → ZMod N) : Finset (ZMod N) :=
  B ∪ affineRowConstants (fun _ : Fin 4 => Finset.univ) (fun j i => theta i (t j))

theorem translatedFrequencyBase_card_le {N ell : Nat} (B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (t : Fin 4 → ZMod N) :
    (translatedFrequencyBase B theta t).card ≤ B.card+4*ell := by
  have h := affineRowConstants_card_le (fun _ : Fin 4 => (Finset.univ : Finset (Fin ell)))
    (fun j i => theta i (t j)) (K := ell) (fun _ => by simp)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left h _)

theorem freiman_bohr_translation {N ell : Nat} [NeZero N] (Gamma : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (h : ∀ i, FreimanHom 2 (bohr Gamma rho) (theta i) ∧ theta i 0 = 0)
    {t u : ZMod N} (ht : t ∈ bohr Gamma (rho/2)) (hu : u ∈ bohr Gamma (rho/4)) :
    ∀ i, theta i (t+u) = theta i t+theta i u := by
  intro i
  have hsum := bohr_mono_radius Gamma (show rho/2+rho/4 ≤ rho by linarith)
    (bohr_add_radius Gamma ht hu)
  have he := (h i).1.isFreimanLinearOn (by decide) t u (t+u) 0
    (bohr_mono_radius Gamma (by linarith : rho/2 ≤ rho) ht)
    (bohr_mono_radius Gamma (by linarith : rho/4 ≤ rho) hu) hsum
    (zero_mem_bohr Gamma hrho) (by ring)
  rw [(h i).2,add_zero] at he
  exact he.symm

theorem translated_frequency_bohr_subset {N ell : Nat} [NeZero N]
    (B : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N) (t : Fin 4 → ZMod N)
    (j : Fin 4) (u : ZMod N) {sigma : Real}
    (haffine : ∀ i, theta i (t j+u) = theta i (t j)+theta i u) :
    freimanFrequencyBohr (translatedFrequencyBase B theta t) theta (sigma/2) u ⊆
      freimanFrequencyBohr B theta sigma (t j+u) := by
  intro z hz
  have hphase := (Finset.mem_filter.mp hz).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
  intro v hv
  rcases Finset.mem_union.mp hv with hvB | hvi
  · have hv' : v ∈ translatedFrequencyBase B theta t ∪ Finset.univ.image (fun i => theta i u) :=
      Finset.mem_union_left _ (Finset.mem_union_left _ hvB)
    have hp := hphase v hv'
    have hn : (0 : Real) ≤ N := Nat.cast_nonneg N
    nlinarith
  · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hvi
    have hc := hphase (theta i (t j)) (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩)))
    have hv := hphase (theta i u) (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
    have hb : (centeredAbs ((theta i (t j)+theta i u)*z) : Real) ≤
        centeredAbs (theta i (t j)*z)+centeredAbs (theta i u*z) := by
      rw [add_mul]
      exact_mod_cast centeredAbs_add_le (theta i (t j)*z) (theta i u*z)
    rw [haffine i]
    linarith

end LeanProofs.GowersSzemeredi
