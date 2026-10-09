import GowersSzemeredi.Proofs16DenseRowSelection
import GowersSzemeredi.Proofs16Corollary20CommonBohr

/-! Put the actual dense-row selected maps on a common Bohr neighborhood,
retaining the directional containment and the exceptional-triple bound. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- The selected maps for the original set have normalized difference maps
on one common neighborhood. Its rank uses the sharper K-1 piece budget. -/
theorem dense_row_common_bohr {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta epsilon : Real} (hdelta : 0 < delta) (heps : 0 < epsilon)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (hN : 8 / epsilon ≤ (N : Real)) :
    let K := denseRowAlphabetBound delta
    let kappa := corollary20Kappa (epsilon / 2) K
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L psi : Fin m → ZMod N → ZMod N)
      (Gamma : Finset (ZMod N)) (T : Finset (ZMod N × ZMod N × ZMod N)),
      (m : Real) * kappa ≤ K - 1 ∧
      (Gamma.card : Real) ≤ (((K : Real) - 1) / kappa) * (16 * kappa ^ (-(2 : Real))) ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ kappa * N ≤ (E i).card ∧
        FreimanHom 2 (bohr Gamma (kappa / (32 * Real.pi))) (psi i) ∧ psi i 0 = 0 ∧
        (∀ x ∈ bohr Gamma (kappa / (32 * Real.pi)),
          ∀ y ∈ bohr Gamma (kappa / (32 * Real.pi)),
          x + y ∈ bohr Gamma (kappa / (32 * Real.pi)) → psi i (x + y) = psi i x + psi i y) ∧
        (∀ x ∈ E i, ∀ y ∈ E i, x - y ∈ bohr Gamma (kappa / (32 * Real.pi)) →
          L i x - L i y = psi i (x - y))) ∧
      (T.card : Real) < epsilon * (N : Real)^3 ∧
      (∀ y z w, (selectedTripleFrequencies L y z w).card ≤ 4 * m) ∧
      ∀ y z w : ZMod N, (y, z, w) ∉ T → y + z ∈ Y → z ∈ Y → y + w ∈ Y → w ∈ Y →
        ∀ d ∈ bohr (selectedTripleFrequencies L y z w) (1 / 16),
          (d, y) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  let K := denseRowAlphabetBound delta
  let kappa := corollary20Kappa (epsilon / 2) K
  have hK : (0 : Real) < K := by exact_mod_cast denseRowAlphabetBound_pos delta
  have hk : 0 < kappa := by dsimp [kappa, corollary20Kappa]; positivity
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨m, E, L, S, T, hm, hE, hT, hrank, hgeom⟩ :=
    dense_row_selected_bohr A Y hdelta heps hdense hN
  obtain ⟨Gamma, hGamma, hB⟩ := common_bohr_extensions E L S
    (fun i => (hE i).2.2.1) (fun i => (hE i).2.2.2)
  have hz : (0 : ZMod N) ∈ bohr Gamma (kappa / (32 * Real.pi)) :=
    zero_mem_bohr Gamma (by positivity)
  have hnonempty (i : Fin m) : (E i).Nonempty := by
    apply Finset.card_pos.mp
    have hp := (mul_pos hk hNR).trans_le (hE i).2.1
    exact_mod_cast hp
  choose psi hpsi hzero hadd hagree using fun i => (hB i).normalized_extension (hnonempty i) hz
  refine ⟨m, E, L, psi, Gamma, T, hm, ?_, ?_, hT, hrank, hgeom⟩
  · have hcount : (m : Real) ≤ ((K : Real) - 1) / kappa := (le_div_iff₀ hk).mpr hm
    exact hGamma.trans (mul_le_mul_of_nonneg_right hcount (by positivity))
  · intro i
    exact ⟨(hE i).1, (hE i).2.1, hpsi i, hzero i, hadd i, hagree i⟩

end LeanProofs.GowersSzemeredi
