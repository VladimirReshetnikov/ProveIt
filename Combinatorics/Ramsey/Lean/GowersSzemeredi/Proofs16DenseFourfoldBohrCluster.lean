import GowersSzemeredi.Proofs16CommonBohrParameters

/-! Localize a dense order-eight Freiman graph into a small Bohr cluster,
with rank, radius, and density independent of the modulus. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem dense_freiman_fourfold_bohr_cluster {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (f : ZMod N → ZMod N) {kappa : Real}
    (hk : 0 < kappa) (hS : kappa*N ≤ (S.card : Real)) (hf : FreimanHom 8 S f) :
    ∃ (Gamma C : Finset (ZMod N)) (psi : ZMod N → ZMod N),
      (Gamma.card : Real) ≤ 16*kappa^(-(2 : Real)) ∧ C ⊆ S ∧
      commonDifferenceClusterDensity kappa*N ≤ (C.card : Real) ∧
      FreimanHom 2 (bohr Gamma (commonDifferenceRadius kappa)) psi ∧ psi 0 = 0 ∧
      ∀ p : Fin 4 → ZMod N, (∀ i, p i ∈ C) →
        fourfoldGraphIndex p ∈ bohr Gamma (commonDifferenceRadius kappa/2) ∧
        psi (fourfoldGraphIndex p) = fourfoldGraphIndex (f ∘ p) := by
  obtain ⟨Gamma,hGamma,hB⟩ := dense_freiman_eight_bohr_extension S f hk hS hf
  let rho := commonDifferenceRadius kappa
  have hrho : 0 < rho := commonDifferenceRadius_pos hk
  obtain ⟨a,C,ha,hCS,hC,hcluster⟩ := exists_dense_bohr_cluster S Gamma hk
    (show 0 ≤ rho/4 by positivity) hS
  let M := commonDifferenceCells kappa
  have hMpos : 0 < M := commonDifferenceCells_pos hk
  letI : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  have hM : 2 ≤ rho/4*(M : Real) := by
    have hceil : 8/rho ≤ (M : Real) := Nat.le_ceil _
    have hmul := (div_le_iff₀ hrho).mp hceil
    nlinarith only [hmul]
  have hCdense := bohr_cluster_density_lower C Gamma M hk.le hM hC
  have hCdense' : commonDifferenceClusterDensity kappa*N ≤ (C.card : Real) :=
    (mul_le_mul_of_nonneg_right (commonDifferenceClusterDensity_le Gamma hk hGamma)
      (Nat.cast_nonneg N)).trans hCdense
  obtain ⟨psi,hpsi,hzero,hrepr⟩ :=
    hB.fourfold_cluster_extension S C Gamma f hrho.le hCS ⟨a,ha⟩ hcluster
  exact ⟨Gamma,C,psi,hGamma,hCS,hCdense',hpsi,hzero,hrepr⟩

end LeanProofs.GowersSzemeredi
