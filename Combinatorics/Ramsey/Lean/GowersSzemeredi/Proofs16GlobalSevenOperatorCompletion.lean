import GowersSzemeredi.Proofs16PatternRowFilling
import GowersSzemeredi.Proofs16GlobalFourRowCompletion

/-! The complete seven-operator implication with explicit remaining
regularity and representation-density hypotheses. These hypotheses are
not consequences of global density proved in this module. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem global_seven_operator_completion {N : Nat} [NeZero N] [Fact N.Prime]
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
      ∀ (C : Finset (ZMod N)), C.Nonempty →
        ∀ (y : ZMod N) (Q : Nat), 0 < Q → 4 ≤ (theta / 2) * Q →
        ∀ (deltaGraph epsilonGraph tau : Real),
        0 < deltaGraph → deltaGraph ≤ 1 → 0 ≤ epsilonGraph → 0 < tau →
        boxSum (fun (d : ↥(bohr F (theta / 2))) (t : ↥C) =>
          edgeIndicator (patternEdge psi J (theta / 2 / 4)) d t - deltaGraph) ≤
          epsilonGraph^4 * ((bohr F (theta / 2)).card : Real)^2 *
            (C.card : Real)^2 →
        tau * (C.card : Real)^3 ≤
          ((patternRepresentationTriples W C y).card : Real) →
        (4 : Real)^(6 * ell + 1) * (12 * epsilonGraph) * (Q : Real)^(6 * ell) ≤
          (deltaGraph^3 * tau)^2 →
        ∀ d ∈ bohr (F ∪ varyingPatternFrequencies psi J y) (theta / 2 / 4 / 2),
          (d, y) ∈ horDiff (verDiff (verDiff (horDiff (verDiff (horDiff (horDiff A)))))) := by
  obtain ⟨m, J, T, F, W, a, psi, hm, hJ, hT, hF, hzero, hWB, hW, hpsi, hvar, hgeom⟩ :=
    global_recentered_patterns_quarter A halpha halpha1 heps hepsbeta hA hN
  have hk : 0 < corollary20Kappa (epsilon / 2) (denseRowAlphabetBound (alpha / 2)) := by
    unfold corollary20Kappa
    have hK : (1 : Real) ≤ denseRowAlphabetBound (alpha / 2) := by
      exact_mod_cast denseRowAlphabetBound_pos (alpha / 2)
    positivity
  refine ⟨m, J, T, F, W, psi, hm, hJ, hT, hF, hzero, hWB, hW, hpsi, hvar, ?_⟩
  intro C hC y Q hQpos hQ deltaGraph epsilonGraph tau hd0 hd1 hepsGraph htau hbox hM hbudget
  letI : NeZero Q := ⟨Nat.ne_of_gt hQpos⟩
  apply pattern_row_filled_rank (horDiff (verDiff (horDiff (horDiff A)))) W C T F psi J a y
    (by positivity) (by positivity) hC hd0 hd1 hepsGraph htau hWB
    (fun i hi => ⟨(hpsi i hi).1, (hpsi i hi).2.1⟩) hgeom hbox hM _ hQ hbudget
  have hcard := Finset.card_union_le F (varyingPatternFrequencies psi J y)
  have hvarcard := hvar y
  omega

end LeanProofs.GowersSzemeredi
