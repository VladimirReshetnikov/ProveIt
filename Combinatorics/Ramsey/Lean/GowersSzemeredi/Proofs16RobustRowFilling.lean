import GowersSzemeredi.Proofs16RobustPatternRepresentations
import GowersSzemeredi.Proofs16PatternRowFilling

/-! Row filling on a constructed proper progression. The witness-density
hypothesis is discharged; the graph quasirandomness and its numerical error
budget remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem robust_pattern_row_filled_rank {N m Q r : Nat} [NeZero N] [NeZero Q]
    (A : Finset (ZMod N × ZMod N)) (W C T F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (a y : ZMod N)
    {alpha rho eta delta epsilon : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) (hWC : W ⊆ C)
    (hrho : 0 ≤ rho) (heta : 0 < eta) (hC : C.Nonempty)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon)
    (hW : W ⊆ bohr T (rho / 4))
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    (hgeom : ∀ t ∈ W, ∀ d ∈ bohr F eta,
      d ∈ bohr (varyingPatternFrequencies psi J t) eta → (d, a + t) ∈ A)
    (hbox : boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
        edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2)
    (hy : y ∈ bohr (commonLargeSpectrum W W (Real.sqrt (alpha^3) / 4)) (1 / (4 * Real.pi)))
    (hK : (F ∪ varyingPatternFrequencies psi J y).card ≤ r) (hQ : 4 ≤ eta * Q)
    (hbudget : (4 : Real)^(r + 1) * (12 * epsilon) * (Q : Real)^r ≤
      (delta^3 * robustRepresentationDensity alpha C)^2) :
    ∀ d ∈ bohr (F ∪ varyingPatternFrequencies psi J y) (eta / 4 / 2),
      (d, y) ∈ horDiff (verDiff (verDiff A)) :=
  pattern_row_filled_rank A W C T F psi J a y hrho heta hC hd0 hd1 heps
    (robustRepresentationDensity_pos ha C hC) hW hpsi hgeom hbox
    ((robust_pattern_representations_exact W C hWC ha hcard).2 y hy) hK hQ hbudget

/-- One quasirandom graph suffices to fill every target row in an actual
proper symmetric progression. Rank and progression size remain explicit. -/
theorem proper_progression_pattern_completion {N m Q r ell : Nat} [NeZero N] [NeZero Q]
    (A : Finset (ZMod N × ZMod N)) (W C T F : Finset (ZMod N))
    (psi : Fin m → ZMod N → ZMod N) (J : Fin 4 → Finset (Fin m)) (a : ZMod N)
    {alpha rho eta delta epsilon : Real} (ha : 0 < alpha)
    (hcard : (W.card : Real) = alpha * N) (hWC : W ⊆ C)
    (hrho : 0 ≤ rho) (heta : 0 < eta) (hC : C.Nonempty)
    (hd0 : 0 < delta) (hd1 : delta ≤ 1) (heps : 0 ≤ epsilon)
    (hW : W ⊆ bohr T (rho / 4))
    (hpsi : ∀ i ∈ J 0 ∪ J 2, FreimanHom 2 (bohr T rho) (psi i) ∧ psi i 0 = 0)
    (hgeom : ∀ t ∈ W, ∀ d ∈ bohr F eta,
      d ∈ bohr (varyingPatternFrequencies psi J t) eta → (d, a + t) ∈ A)
    (hbox : boxSum (fun (d : ↥(bohr F eta)) (t : ↥C) =>
        edgeIndicator (patternEdge psi J (eta / 4)) d t - delta) ≤
      epsilon^4 * ((bohr F eta).card : Real)^2 * (C.card : Real)^2)
    (hJ : ∀ i, (J i).card ≤ ell) (hF : F.card + 2 * ell ≤ r) (hQ : 4 ≤ eta * Q)
    (hbudget : (4 : Real)^(r + 1) * (12 * epsilon) * (Q : Real)^r ≤
      (delta^3 * robustRepresentationDensity alpha C)^2) :
    ∃ S : Finset (ZMod N), ∃ P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N,
      (S.card : Real) ≤ 16 / alpha^2 ∧ P.rank ≤ S.card + 1 ∧ P.Proper ∧
      0 ∈ P.carrier ∧ (∀ y ∈ P.carrier, -y ∈ P.carrier) ∧
      P.carrier ⊆ bohr T rho ∧
      Real.exp (-(((S.card : Real) + 1) * Real.log (1 + Real.pi) +
        10 * ((S.card : Real) + 1)^2)) * N ≤ P.carrier.card ∧
      ∀ y ∈ P.carrier, ∀ d ∈ bohr (F ∪ varyingPatternFrequencies psi J y) (eta / 4 / 2),
        (d, y) ∈ horDiff (verDiff (verDiff A)) := by
  obtain ⟨S, P, hS, hPR, hPproper, hP0, hPneg, hPT, hPcard, hcount⟩ :=
    exists_proper_progression_with_many_representations W C T hWC ha hcard hW
  refine ⟨S, P, hS, hPR, hPproper, hP0, hPneg, hPT, hPcard, ?_⟩
  intro y hy
  have hK : (F ∪ varyingPatternFrequencies psi J y).card ≤ r :=
    (Finset.card_union_le _ _).trans
      ((Nat.add_le_add_left (varyingPatternFrequencies_card_le psi J hJ y) _).trans hF)
  exact pattern_row_filled_rank A W C T F psi J a y hrho heta hC hd0 hd1 heps
    (robustRepresentationDensity_pos ha C hC) hW hpsi hgeom hbox (hcount y hy) hK hQ hbudget

end LeanProofs.GowersSzemeredi
