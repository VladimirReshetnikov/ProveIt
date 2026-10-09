import GowersSzemeredi.Proofs16FourRowCompletion

/-! Global-density geometry and the six-operator conclusion conditional
on an actual triple witness. Producing those witnesses uniformly remains
the role of the regularity and common-neighborhood arguments. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_four_row_completion {N : Nat} [NeZero N] [Fact N.Prime]
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
      (T F W : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N),
      (m : Real) * kappa ≤ K - 1 ∧ (∀ i, (J i).card ≤ ell) ∧
      (T.card : Real) ≤ (2 * ell : Nat) * (16 * kappa ^ (-(2 : Real))) ∧
      F.card ≤ 4 * ell ∧ (0 : ZMod N) ∈ W ∧ W ⊆ bohr T (rho / 4) ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) *
        (bohr T (rho / 4 / 2)).card ≤ (W.card : Real) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ t, (varyingPatternFrequencies psi J t).card ≤ 2 * ell) ∧
      ∀ y d, d ∈ bohr F (theta / 2) →
        d ∈ bohr (varyingPatternFrequencies psi J y) (theta / 2 / 4) →
        (∃ x₁ ∈ W, ∃ x₂ ∈ W, ∃ x₃ ∈ W, x₁ + x₂ - x₃ - y ∈ W ∧
          d ∈ bohr (varyingPatternFrequencies psi J x₁) (theta / 2 / 4) ∧
          d ∈ bohr (varyingPatternFrequencies psi J x₂) (theta / 2 / 4) ∧
          d ∈ bohr (varyingPatternFrequencies psi J x₃) (theta / 2 / 4)) →
        (d, y) ∈ verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A))))) := by
  obtain ⟨m, J, T, F, W, a, psi, hm, hJ, hT, hF, hzero, hWB, hW, hpsi, hvar, hgeom⟩ :=
    global_recentered_patterns_quarter A halpha halpha1 heps hepsbeta hA hN
  have hk : 0 < corollary20Kappa (epsilon / 2) (denseRowAlphabetBound (alpha / 2)) := by
    unfold corollary20Kappa
    have hK : (1 : Real) ≤ denseRowAlphabetBound (alpha / 2) := by
      exact_mod_cast denseRowAlphabetBound_pos (alpha / 2)
    positivity
  refine ⟨m, J, T, F, W, psi, hm, hJ, hT, hF, hzero, hWB, hW, hpsi, hvar, ?_⟩
  intro y d hc hd hwitness
  exact recentered_four_row_of_triple (horDiff (verDiff (horDiff (horDiff A)))) W T F psi J a
    (by positivity) (by positivity) hWB (fun i hi => ⟨(hpsi i hi).1, (hpsi i hi).2.1⟩)
    hgeom hc hd hwitness

end LeanProofs.GowersSzemeredi
