import GowersSzemeredi.Proofs16FourfoldGraphMap
import GowersSzemeredi.Proofs16BohrRecentering

/-! Fourfold graph differences in a small cluster agree with a normalized
Freiman extension on the full Bohr neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem fourfold_cluster_mem_bohr {N : Nat} [NeZero N]
    (S Gamma : Finset (ZMod N)) {rho : Real}
    (hcluster : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ bohr Gamma (rho/4))
    (p : Fin 4 → ZMod N) (hp : ∀ i, p i ∈ S) :
    fourfoldGraphIndex p ∈ bohr Gamma (rho/2) := by
  rw [show rho/4 = (rho/2)/2 by ring] at hcluster
  have h := bohr_add_half (ρ := rho/2) (hcluster (p 0) (hp 0) (p 1) (hp 1))
    (neg_mem_bohr (hcluster (p 2) (hp 2) (p 3) (hp 3)))
  simpa only [fourfoldGraphIndex,sub_eq_add_neg] using h

theorem IsBHomomorphism.fourfold_cluster_extension {N : Nat} [NeZero N]
    (E S Gamma : Finset (ZMod N)) (f : ZMod N → ZMod N) {rho : Real}
    (hrho : 0 ≤ rho) (hSE : S ⊆ E) (hSne : S.Nonempty)
    (hF : IsBHomomorphism E (bohr Gamma rho) f)
    (hcluster : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ bohr Gamma (rho/4)) :
    ∃ psi : ZMod N → ZMod N, FreimanHom 2 (bohr Gamma rho) psi ∧ psi 0 = 0 ∧
      ∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ S) →
        fourfoldGraphIndex p ∈ bohr Gamma (rho/2) ∧
        psi (fourfoldGraphIndex p) = fourfoldGraphIndex (f ∘ p) := by
  obtain ⟨psi,hpsi,hzero,_,hagree⟩ :=
    hF.normalized_extension (hSne.mono hSE) (zero_mem_bohr Gamma hrho)
  refine ⟨psi,hpsi,hzero,?_⟩
  intro p hp
  have hpair (i j : Fin 4) : p i-p j ∈ bohr Gamma rho :=
    bohr_mono_radius Gamma (by linarith : rho/4 ≤ rho) (hcluster _ (hp i) _ (hp j))
  have hindex := fourfold_cluster_mem_bohr S Gamma hcluster p hp
  have hfull : fourfoldGraphIndex p ∈ bohr Gamma rho :=
    bohr_mono_radius Gamma (by linarith : rho/2 ≤ rho) hindex
  have hlin := hpsi.add_eq_add hfull (hpair 2 3) (hpair 0 1)
    (zero_mem_bohr Gamma hrho) (by dsimp [fourfoldGraphIndex]; ring)
  have h01 := hagree _ (hSE (hp 0)) _ (hSE (hp 1)) (hpair 0 1)
  have h23 := hagree _ (hSE (hp 2)) _ (hSE (hp 3)) (hpair 2 3)
  refine ⟨hindex,?_⟩
  dsimp [fourfoldGraphIndex,Function.comp_def] at hlin ⊢
  rw [hzero] at hlin
  linear_combination hlin-h01+h23

end LeanProofs.GowersSzemeredi
