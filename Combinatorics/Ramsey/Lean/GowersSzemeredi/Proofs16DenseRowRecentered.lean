import GowersSzemeredi.Proofs16DenseRowCommonBohr
import GowersSzemeredi.Proofs16BohrRecentering

/-! Recenter the actual dense-row selected pieces while preserving their
common difference maps and the original directional containment. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Every selected piece has a dense cluster on which its affine part is
its original value at the chosen center and its linear part is the same
normalized difference map on the common Bohr neighborhood. -/
theorem dense_row_common_bohr_recentered {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta epsilon : Real} (hdelta : 0 < delta) (heps : 0 < epsilon)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (hN : 8 / epsilon ≤ (N : Real)) :
    let K := denseRowAlphabetBound delta
    let kappa := corollary20Kappa (epsilon / 2) K
    ∃ (m : Nat) (E : Fin m → Finset (ZMod N)) (L psi : Fin m → ZMod N → ZMod N)
      (Gamma : Finset (ZMod N)) (T : Finset (ZMod N × ZMod N × ZMod N))
      (a : Fin m → ZMod N) (C : Fin m → Finset (ZMod N)),
      (m : Real) * kappa ≤ K - 1 ∧
      (Gamma.card : Real) ≤ (((K : Real) - 1) / kappa) * (16 * kappa ^ (-(2 : Real))) ∧
      (∀ i, FreimanHom 8 (E i) (L i) ∧ kappa * N ≤ (E i).card ∧
        FreimanHom 2 (bohr Gamma (kappa / (32 * Real.pi))) (psi i) ∧ psi i 0 = 0 ∧
        (∀ x ∈ bohr Gamma (kappa / (32 * Real.pi)),
          ∀ y ∈ bohr Gamma (kappa / (32 * Real.pi)),
          x + y ∈ bohr Gamma (kappa / (32 * Real.pi)) → psi i (x + y) = psi i x + psi i y) ∧
        (∀ x ∈ E i, ∀ y ∈ E i, x - y ∈ bohr Gamma (kappa / (32 * Real.pi)) →
          L i x - L i y = psi i (x - y))) ∧
      (∀ i, a i ∈ C i ∧ C i ⊆ E i ∧
        kappa * (bohr Gamma ((kappa / (32 * Real.pi)) / 2)).card ≤ ((C i).card : Real) ∧
        (∀ x ∈ C i, ∀ y ∈ C i, x - y ∈ bohr Gamma (kappa / (32 * Real.pi))) ∧
        ∀ x ∈ C i, L i x = L i (a i) + psi i (x - a i)) ∧
      (T.card : Real) < epsilon * (N : Real)^3 ∧
      (∀ y z w, (selectedTripleFrequencies L y z w).card ≤ 4 * m) ∧
      ∀ y z w : ZMod N, (y, z, w) ∉ T → y + z ∈ Y → z ∈ Y → y + w ∈ Y → w ∈ Y →
        ∀ d ∈ bohr (selectedTripleFrequencies L y z w) (1 / 16),
          (d, y) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  let K := denseRowAlphabetBound delta
  let kappa := corollary20Kappa (epsilon / 2) K
  have hK : (0 : Real) < K := by exact_mod_cast denseRowAlphabetBound_pos delta
  have hk : 0 < kappa := by dsimp [kappa, corollary20Kappa]; positivity
  have hrho : 0 ≤ kappa / (32 * Real.pi) := by positivity
  obtain ⟨m, E, L, psi, Gamma, T, hm, hGamma, hE, hT, hrank, hgeom⟩ :=
    dense_row_common_bohr A Y hdelta heps hdense hN
  choose a C ha hCE hcard hdiff using fun i =>
    exists_dense_bohr_cluster (E i) Gamma hk hrho (hE i).2.1
  refine ⟨m, E, L, psi, Gamma, T, a, C, hm, hGamma, hE, ?_, hT, hrank, hgeom⟩
  intro i
  refine ⟨ha i, hCE i, hcard i, hdiff i, ?_⟩
  intro x hx
  have h := (hE i).2.2.2.2.2 x (hCE i hx) (a i) (hCE i (ha i)) (hdiff i x hx (a i) (ha i))
  linear_combination h

end LeanProofs.GowersSzemeredi
