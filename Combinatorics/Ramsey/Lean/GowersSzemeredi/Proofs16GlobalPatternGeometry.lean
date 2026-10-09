import GowersSzemeredi.Proofs16DenseRowPatternRecentering
import GowersSzemeredi.Proofs16DenseRowExtraction

/-! The normalized fixed-pattern geometry starting only from the global
density of a subset of the prime cyclic square. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Global density supplies both the dense rows and the common normalized
parameter geometry, with the sharp first-moment row-density factor. -/
theorem global_recentered_patterns {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) {alpha epsilon : Real}
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) (heps : 0 < epsilon)
    (hepsbeta : epsilon < (alpha / (2 - alpha))^4)
    (hA : alpha * (N : Real)^2 ≤ A.card) (hN : 8 / epsilon ≤ (N : Real)) :
    let delta := alpha / 2
    let beta := alpha / (2 - alpha)
    let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
    let R := directionalQuarterSpanCutoff r 64 (1 / (8 * Real.pi))
    let ell := spanGeneratorBound r R
    let K := denseRowAlphabetBound delta
    let kappa := corollary20Kappa (epsilon / 2) K
    let rho := kappa / (32 * Real.pi)
    let theta : Real := 1 / (16 * (max 1 ell : Nat))
    ∃ (m : Nat) (J : Fin 4 → Finset (Fin m))
      (T F W : Finset (ZMod N)) (a : ZMod N) (psi : Fin m → ZMod N → ZMod N),
      (m : Real) * kappa ≤ K - 1 ∧ (∀ i, (J i).card ≤ ell) ∧
      (T.card : Real) ≤ (2 * ell : Nat) * (16 * kappa ^ (-(2 : Real))) ∧
      F.card ≤ 4 * ell ∧ (0 : ZMod N) ∈ W ∧ W ⊆ bohr T rho ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) *
        (bohr T (rho / 2)).card ≤ (W.card : Real) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ t, (varyingPatternFrequencies psi J t).card ≤ 2 * ell) ∧
      ∀ t ∈ W, ∀ d ∈ bohr F (theta / 2),
        d ∈ bohr (varyingPatternFrequencies psi J t) (theta / 2) →
          (d, a + t) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  obtain ⟨Y, hY, hrows⟩ := exists_dense_rows A halpha halpha1 hA
  have hden : 0 < 2 - alpha := by linarith
  exact dense_row_recentered_patterns A Y (by positivity)
    (div_nonneg halpha.le hden.le) heps hepsbeta hrows hY hN

end LeanProofs.GowersSzemeredi
