import GowersSzemeredi.Proofs16GraphCoverRetention
import GowersSzemeredi.Proofs16DenseFourfoldBohrCluster

/-! Dense mixed configurations admit one common difference map defined
on a full Bohr neighborhood, with retained indices in its half-radius part. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem mixed_configurations_common_bohr_map {N : Nat} [NeZero N]
    (A B : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : Q ⊆ mixedColumnQuadruples Finset.univ f)
    (hA : ∀ q ∈ Q, q 0 ∈ A) (hB : ∀ q ∈ Q, q 1 ∈ B)
    (hf : IsFreimanLinearOn A (f 0)) (hg : FreimanHom 8 B (f 1))
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ (Gamma : Finset (ZMod N)) (psi : ZMod N → ZMod N)
      (a c : ZMod N) (R : Finset (Fin 4 → ZMod N)),
      (Gamma.card : Real) ≤ 16*delta^(-(2 : Real)) ∧
      FreimanHom 2 (bohr Gamma (commonDifferenceRadius delta)) psi ∧ psi 0 = 0 ∧
      R ⊆ Q ∧ commonDifferenceBohrDensity delta*(N : Real)^3 ≤ R.card ∧
      ∀ q ∈ R, q 0-q 1-a ∈ bohr Gamma (commonDifferenceRadius delta/2) ∧
        f 0 (q 0)-f 1 (q 1) = c+psi (q 0-q 1-a) := by
  obtain ⟨a,c,S,hSB,hS,hagree⟩ := mixed_configurations_dense_overlap A B f Q hQ hA hB hcount
  have hgS : FreimanHom 8 S (f 1) := IsAddFreimanHom.subset hSB hg (Set.mapsTo_univ _ _)
  obtain ⟨Gamma,C,psi,hGamma,hCS,hC,hpsi,hzero,hrepr⟩ :=
    dense_freiman_fourfold_bohr_cluster S (f 1) hdelta hS hgS
  have hg2 : IsFreimanLinearOn B (f 1) := hg.isFreimanLinearOn (by decide)
  obtain ⟨b,d,R,hRQ,hR,hvalue⟩ := common_graph_cover_retained_fibre A B C f Q a c
    (hCS.trans hSB) (fun s hs => hagree s (hCS hs)) hA hB hf hg2
    (commonDifferenceClusterDensity_pos hdelta) hC hdelta hcount psi (fun p hp => (hrepr p hp).2)
  refine ⟨Gamma,psi,b,d,R,hGamma,hpsi,hzero,hRQ,hR,?_⟩
  intro q hq
  obtain ⟨hindex,hval⟩ := hvalue q hq
  obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hindex
  have hp' : ∀ i, p i ∈ C := by simpa only [Fintype.mem_piFinset] using hp
  exact ⟨he ▸ (hrepr p hp').1,hval⟩

end LeanProofs.GowersSzemeredi
