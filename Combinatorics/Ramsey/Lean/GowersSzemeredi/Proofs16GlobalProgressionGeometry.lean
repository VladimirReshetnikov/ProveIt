import GowersSzemeredi.Proofs16FixedPatternProgression
import GowersSzemeredi.Proofs16DenseRowExtraction
import GowersSzemeredi.Proofs16FixedBohrPatterns

/-! Proper symmetric progression geometry from global density. The
selected maps are normalized on a Bohr domain containing all four-term
combinations of progression points. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_proper_progression_geometry {N : Nat} [NeZero N] [Fact N.Prime]
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
    let width := Real.log (1 + rho⁻¹)
    let theta : Real := 1 / (16 * (max 1 ell : Nat))
    ∃ (m : Nat) (J : Fin 4 → Finset (Fin m)) (T F : Finset (ZMod N))
      (Q : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (t : ZMod N) (W : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N),
      (m : Real) * kappa ≤ K - 1 ∧ (∀ i, (J i).card ≤ ell) ∧
      (T.card : Real) ≤ (2 * ell : Nat) * (16 * kappa ^ (-(2 : Real))) ∧
      F.card ≤ 4 * ell ∧ Q.rank ≤ T.card + 1 ∧ Q.Proper ∧
      (0 : ZMod N) ∈ Q.carrier ∧ (∀ x ∈ Q.carrier, -x ∈ Q.carrier) ∧
      Q.carrier ⊆ bohr T (rho / 4) ∧ W.Nonempty ∧ W ⊆ Q.carrier ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) * Q.carrier.card ≤ (W.card : Real) ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) *
        Real.exp (-(((T.card : Real) + 1) * width + 10 * ((T.card : Real) + 1)^2)) * N ≤
          (W.card : Real) ∧
      (∀ x₁ ∈ Q.carrier, ∀ x₂ ∈ Q.carrier, ∀ x₃ ∈ Q.carrier, ∀ x₄ ∈ Q.carrier,
        x₁ + x₂ - x₃ - x₄ ∈ bohr T rho) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0 ∧
        ∀ x ∈ bohr T rho, ∀ y ∈ bohr T rho, x + y ∈ bohr T rho →
          psi i (x + y) = psi i x + psi i y) ∧
      (∀ x, (varyingPatternFrequencies psi J x).card ≤ 2 * ell) ∧
      ∀ x ∈ W, ∀ d ∈ bohr F (theta / 2),
        d ∈ bohr (varyingPatternFrequencies psi J x) (theta / 2) →
          (d, t + x) ∈ horDiff (verDiff (horDiff (horDiff A))) := by
  let delta := alpha / 2
  let beta := alpha / (2 - alpha)
  let r := ⌈16 * delta ^ (-(2 : Real))⌉₊
  let R := directionalQuarterSpanCutoff r 64 (1 / (8 * Real.pi))
  let ell := spanGeneratorBound r R
  let K := denseRowAlphabetBound delta
  let kappa := corollary20Kappa (epsilon / 2) K
  let rho := kappa / (32 * Real.pi)
  obtain ⟨Y, hY, hrows⟩ := exists_dense_rows A halpha halpha1 hA
  have hden : 0 < 2 - alpha := by linarith
  obtain ⟨m, E, L, S, J, z, w, V, hm, hE, hJ, hV, hfreq, hgeom⟩ :=
    dense_row_fixed_bohr_patterns A Y (show 0 < delta by positivity)
      (div_nonneg halpha.le hden.le) heps hrows hY hN
  let nu := (beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)
  have hcount : (0 : Real) < ((m + 1 : Nat)^(4 * ell) : Real) := by positivity
  have hnu : 0 < nu := div_pos (sub_pos.mpr hepsbeta) hcount
  have hVnu : nu * N ≤ V.card := by
    dsimp [nu]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hcount).mpr
    nlinarith only [hV]
  have hk : 0 < kappa := by
    dsimp [kappa, corollary20Kappa]
    have hK : (1 : Real) ≤ K := by exact_mod_cast denseRowAlphabetBound_pos delta
    positivity
  have hrho : 0 < rho := by positivity
  obtain ⟨hw0, hwidth⟩ := logarithmic_bohr_width hrho
  obtain ⟨T, F, Q, t, W, psi, hT, hF, hQr, hQp, hQB, hWne, hWQ, hW, hWglobal,
    hfour, hpsi, hvar, hpropergeom⟩ :=
    fixed_patterns_on_proper_progression (horDiff (verDiff (horDiff (horDiff A)))) V E L S J z w
      hnu hVnu hrho (show 0 ≤ 16 * kappa ^ (-(2 : Real)) by positivity)
      (show 0 ≤ (1 : Real) / (16 * (max 1 ell : Nat)) by positivity)
      hw0 hwidth hJ (fun i => (hE i).2.2.1) (fun i => (hE i).2.2.2)
      (fun y hy => ⟨(hgeom y hy).1, (hgeom y hy).2.2.1⟩)
      (fun y hy => (hgeom y hy).2.2.2.2)
  exact ⟨m, J, T, F, Q, t, W, psi, hm, hJ, hT, hF, hQr, hQp,
    centered_progression_zero_mem Q, fun x hx => centered_progression_neg_mem Q hx,
    hQB, hWne, hWQ, hW, hWglobal, hfour, hpsi, hvar, fun x hx => (hpropergeom x hx).2⟩

end LeanProofs.GowersSzemeredi
