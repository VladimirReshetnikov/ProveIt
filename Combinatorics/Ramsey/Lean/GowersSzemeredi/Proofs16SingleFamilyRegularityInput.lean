import GowersSzemeredi.Proofs16CoherentQuasirandomDomain

/-! The globally constructed single progression family supplies the full
Bohr-domain input of coherent regularity, with the original anchor maps. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem IsSingleCoherentProgression.regularity_input {N d ell : Nat} [NeZero N]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    {P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N} {B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {x y : ZMod N → ZMod N}
    {t : Fin 4 → ZMod N} {color : ZMod N → Fin 4} {X : Finset (ZMod N)}
    {Q : Finset (Fin 4 → ZMod N)}
    (h : IsSingleCoherentProgression H T L delta kappa d r P B theta x y t color X Q) :
    ∃ Gamma : Finset (ZMod N),
      Gamma.card ≤ rowCommonBohrRank delta (uniformAnchorIndexDensity delta kappa d r) d r ∧
      B.card ≤ 8*jointSelectionRank d r ∧ ell ≤ 8*jointSelectionRank d r ∧
      X ⊆ bohr Gamma ((1/(8*Real.pi))/4) ∧
      (∀ i, FreimanHom 2 (bohr Gamma (1/(8*Real.pi))) (theta i) ∧ theta i 0 = 0) ∧
      singleProgressionDensity delta kappa d r*(N : Real)^3 ≤ Q.card ∧
      CoherentFrequencyFamily X B theta
        (fun u => shiftAnchorMap T L r x y (t (color u)+u)) (jointSelectionRadius d r/2) Q := by
  obtain ⟨hPrank,hPproper,hPmass,hB,hell,hthetaP,hfrequency,ht,hXP,hX,hQ,hlocal,hcoherent⟩ := h
  obtain ⟨Gamma,hG,hPsub,htheta⟩ := hfrequency
  refine ⟨Gamma,hG,hB,hell,hXP.trans hPsub,htheta,hQ,?_,?_⟩
  · intro u hu
    exact ⟨(hlocal u hu).1,(hlocal u hu).2.1⟩
  · intro b hb
    exact ⟨(hcoherent b hb).1,fun j => ((hcoherent b hb).2.2.1 j).1,(hcoherent b hb).2.2.2.2⟩

theorem jointSelectionRadius_half_lt_quarter (d : Nat) (r : Real) :
    jointSelectionRadius d r/2 < 1/4 := by
  have hp : 0 ≤ Real.pi*(jointSelectionRank d r : Real) := by positivity
  have h : jointSelectionRadius d r < 1/2 := by
    change 1/(128*Real.pi*((jointSelectionRank d r : Real)+1)) < 1/2
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Real.pi_gt_three]
  linarith

end LeanProofs.GowersSzemeredi
