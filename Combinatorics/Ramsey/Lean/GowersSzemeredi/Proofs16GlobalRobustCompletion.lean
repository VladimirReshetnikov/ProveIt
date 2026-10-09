import GowersSzemeredi.Proofs16GlobalProgressionGeometry
import GowersSzemeredi.Proofs16RobustRowFilling

/-! Global density now supplies proper parameter progressions and all
representation counts. Completing the seven operators still requires the
stated quasirandom graph estimate at the displayed error budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_robust_seven_operator_completion {N : Nat} [NeZero N] [Fact N.Prime]
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
    ∃ (m : Nat) (J : Fin 4 → Finset (Fin m)) (T F S : Finset (ZMod N))
      (Q P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N)
      (W : Finset (ZMod N)) (psi : Fin m → ZMod N → ZMod N),
      let sigma := (W.card : Real) / N
      let tau := robustRepresentationDensity sigma Q.carrier
      (m : Real) * kappa ≤ K - 1 ∧ (∀ i, (J i).card ≤ ell) ∧
      (T.card : Real) ≤ (2 * ell : Nat) * (16 * kappa ^ (-(2 : Real))) ∧
      F.card ≤ 4 * ell ∧ Q.rank ≤ T.card + 1 ∧ Q.Proper ∧
      Q.carrier ⊆ bohr T (rho / 4) ∧ W.Nonempty ∧ W ⊆ Q.carrier ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) * Q.carrier.card ≤ (W.card : Real) ∧
      ((beta^4 - epsilon) / ((m + 1 : Nat)^(4 * ell) : Real)) *
        Real.exp (-(((T.card : Real) + 1) * width + 10 * ((T.card : Real) + 1)^2)) * N ≤
          (W.card : Real) ∧
      (∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0) ∧
      0 < sigma ∧ 0 < tau ∧ (S.card : Real) ≤ 16 / sigma^2 ∧
      P.rank ≤ S.card + 1 ∧ P.Proper ∧ 0 ∈ P.carrier ∧
      (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧ P.carrier ⊆ bohr T rho ∧
      Real.exp (-(((S.card : Real) + 1) * Real.log (1 + Real.pi) +
        10 * ((S.card : Real) + 1)^2)) * N ≤ P.carrier.card ∧
      (∀ y ∈ P.carrier, tau * (Q.carrier.card : Real)^3 ≤
        ((patternRepresentationTriples W Q.carrier y).card : Real)) ∧
      ∀ (q : Nat), 0 < q → 4 ≤ (theta / 2) * q →
        ∀ (deltaGraph epsilonGraph : Real),
        0 < deltaGraph → deltaGraph ≤ 1 → 0 ≤ epsilonGraph →
        boxSum (fun (d : ↥(bohr F (theta / 2))) (t : ↥Q.carrier) =>
          edgeIndicator (patternEdge psi J (theta / 2 / 4)) d t - deltaGraph) ≤
          epsilonGraph^4 * ((bohr F (theta / 2)).card : Real)^2 *
            (Q.carrier.card : Real)^2 →
        (4 : Real)^(6 * ell + 1) * (12 * epsilonGraph) * (q : Real)^(6 * ell) ≤
          (deltaGraph^3 * tau)^2 →
        ∀ y ∈ P.carrier, ∀ d ∈ bohr (F ∪ varyingPatternFrequencies psi J y) (theta / 2 / 4 / 2),
          (d, y) ∈ horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
  obtain ⟨m, J, T, F, Q, a, W, psi, hm, hJ, hT, hF, hQR, hQproper, hQ0, hQneg,
    hQB, hWne, hWQ, hWrel, hWambient, hfour, hpsi, hvar, hgeom⟩ :=
    global_proper_progression_geometry A halpha halpha1 heps hepsbeta hA hN
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let sigma := (W.card : Real) / N
  have hsigma : 0 < sigma := div_pos (by exact_mod_cast hWne.card_pos) hNR
  have hcard : (W.card : Real) = sigma * N := by dsimp [sigma]; field_simp
  have hQne : Q.carrier.Nonempty := ⟨0, hQ0⟩
  have htau := robustRepresentationDensity_pos hsigma Q.carrier hQne
  obtain ⟨S, P, hS, hPR, hPproper, hP0, hPneg, hPB, hPcard, hcount⟩ :=
    exists_proper_progression_with_many_representations W Q.carrier T hWQ hsigma hcard (hWQ.trans hQB)
  have hk : 0 < corollary20Kappa (epsilon / 2) (denseRowAlphabetBound (alpha / 2)) := by
    unfold corollary20Kappa
    have hK : (1 : Real) ≤ denseRowAlphabetBound (alpha / 2) := by
      exact_mod_cast denseRowAlphabetBound_pos (alpha / 2)
    positivity
  refine ⟨m, J, T, F, S, Q, P, W, psi, hm, hJ, hT, hF, hQR, hQproper,
    hQB, hWne, hWQ, hWrel, hWambient, fun i hi => ⟨(hpsi i hi).1, (hpsi i hi).2.1⟩,
    hsigma, htau, hS, hPR, hPproper, hP0, hPneg, hPB, hPcard, hcount, ?_⟩
  intro q hqpos hq deltaGraph epsilonGraph hd0 hd1 hepsGraph hbox hbudget y hy
  letI : NeZero q := ⟨Nat.ne_of_gt hqpos⟩
  apply pattern_row_filled_rank (horDiff (verDiff (horDiff (horDiff A)))) W Q.carrier T F psi J a y
    (by positivity) (by positivity) hQne hd0 hd1 hepsGraph htau (hWQ.trans hQB)
    (fun i hi => ⟨(hpsi i hi).1, (hpsi i hi).2.1⟩) hgeom hbox (hcount y hy) _ hq hbudget
  have hcard := Finset.card_union_le F (varyingPatternFrequencies psi J y)
  have hvarcard := hvar y
  omega

end LeanProofs.GowersSzemeredi
