import GowersSzemeredi.Proofs16GlobalPatternGeometry

/-! The centered parameters lie in a quarter-radius neighborhood, while
the normalized maps retain their full-radius domains. The averaging cost
uses the eighth-radius neighborhood. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem dense_row_recentered_patterns_quarter {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (Y : Finset (ZMod N))
    {delta beta epsilon : Real} (hdelta : 0 < delta) (hbeta : 0 ≤ beta)
    (heps : 0 < epsilon) (hepsbeta : epsilon < beta^4)
    (hdense : ∀ y ∈ Y, delta ≤ (rowOf A y).card / (N : Real))
    (hY : beta * N ≤ Y.card) (hN : 8 / epsilon ≤ (N : Real)) :
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
      F.card ≤ 4 * ell ∧ (0 : ZMod N) ∈ W ∧ W ⊆ bohr T (rho / 4) ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) *
        (bohr T (rho / 4 / 2)).card ≤ (W.card : Real) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ t, (varyingPatternFrequencies psi J t).card ≤ 2 * ell) ∧
      ∀ t ∈ W, ∀ d ∈ bohr F (theta / 2),
        d ∈ bohr (varyingPatternFrequencies psi J t) (theta / 2) →
          (d, a + t) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
  let R := directionalQuarterSpanCutoff r 64 (1 / (8 * Real.pi))
  let ell := spanGeneratorBound r R
  let K := denseRowAlphabetBound delta
  let kappa := corollary20Kappa (epsilon / 2) K
  obtain ⟨m, E, L, S, J, z, w, V, hm, hE, hJ, hV, hfreq, hgeom⟩ :=
    dense_row_fixed_bohr_patterns A Y hdelta hbeta heps hdense hY hN
  let nu := (beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)
  have hden : (0 : Real) < ((m + 1 : Nat)^(4 * ell) : Real) := by positivity
  have hnu : 0 < nu := div_pos (sub_pos.mpr hepsbeta) hden
  have hVnu : nu * N ≤ V.card := by
    dsimp [nu]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hV]
  have hk : 0 < kappa := by
    dsimp [kappa, corollary20Kappa]
    have hK : (1 : Real) ≤ K := by exact_mod_cast denseRowAlphabetBound_pos delta
    positivity
  obtain ⟨T, F, W, a, psi, hT, hF, hzero, hWB, hW, hpsi, hvar, hrec⟩ :=
    fixed_patterns_recentered_radius (horDiff (verDiff (horDiff (horDiff A)))) V E L S J z w
      hnu hVnu (show 0 ≤ kappa / (32 * Real.pi) by positivity)
      (show 0 ≤ kappa / (32 * Real.pi) / 4 by positivity)
      (show kappa / (32 * Real.pi) / 4 ≤ kappa / (32 * Real.pi) by
        have : 0 ≤ kappa / (32 * Real.pi) := by positivity
        linarith)
      (show 0 ≤ 16 * kappa ^ (-(2 : Real)) by positivity)
      (show 0 ≤ (1 : Real) / (16 * (max 1 ell : Nat)) by positivity)
      hJ (fun i => (hE i).2.2.1) (fun i => (hE i).2.2.2)
      (fun y hy => ⟨(hgeom y hy).1, (hgeom y hy).2.2.1⟩)
      (fun y hy => (hgeom y hy).2.2.2.2)
  exact ⟨m, J, T, F, W, a, psi, hm, hJ, hT, hF, hzero, hWB, hW, hpsi, hvar,
    fun t ht => (hrec t ht).2⟩


theorem global_recentered_patterns_quarter {N : Nat} [NeZero N] [Fact N.Prime]
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
      F.card ≤ 4 * ell ∧ (0 : ZMod N) ∈ W ∧ W ⊆ bohr T (rho / 4) ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) *
        (bohr T (rho / 4 / 2)).card ≤ (W.card : Real) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ t, (varyingPatternFrequencies psi J t).card ≤ 2 * ell) ∧
      ∀ t ∈ W, ∀ d ∈ bohr F (theta / 2),
        d ∈ bohr (varyingPatternFrequencies psi J t) (theta / 2) →
          (d, a + t) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  obtain ⟨Y, hY, hrows⟩ := exists_dense_rows A halpha halpha1 hA
  have hden : 0 < 2 - alpha := by linarith
  exact dense_row_recentered_patterns_quarter A Y (by positivity)
    (div_nonneg halpha.le hden.le) heps hepsbeta hrows hY hN


end LeanProofs.GowersSzemeredi
