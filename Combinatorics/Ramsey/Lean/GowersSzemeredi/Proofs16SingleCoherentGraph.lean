import GowersSzemeredi.Proofs16SingleCoherentGraphParameters

/-! Apply adaptive regularity to the actual original anchor family, with
all cell, radius, density and uniform modulus conditions discharged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasSingleCoherentGraph {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (delta kappa : Real) (d : Nat) (r : Real) (power : Nat) (scale : Real) : Prop :=
  let H := singleCoherentGraphH d r
  let m := coherentGraphFrequencyBound B.card ell
  let e := coherentDensityAccuracy H m power scale
  let initial := (singleCoherentGraphInitialRank delta kappa d r,singleProgressionDensity delta kappa d r)
  ∃ Gamma : Finset (ZMod N), Gamma.card ≤ initial.1 ∧
  ∃ s : Nat, s ≤ ell ∧
  let final := (coherentAdaptiveGraphState e H m singleCoherentGraphCells ell (1/(8*Real.pi)))^[s] initial
  let tau := (jointSelectionRadius d r/2)/(2 : Real)^s
  ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N))
    (source : ZMod N → ZMod N) (density : Real),
    IsCoherentFrequencyRefinement Q X Gamma B theta F (1/(8*Real.pi)) tau
      final.2 final.1 (B.card+4*s*ell) (4^s) S B' V R source ∧
    B'.card ≤ final.1 ∧ 0 < final.2 ∧
    (1/((4*H : Nat) : Real)^m)/2 ≤ density ∧ density ≤ 1 ∧
    boxSum (fun (z : ↥(bohr B' tau)) (u : ↥(bohr S ((1/(8*Real.pi))/4))) =>
      (if (z : ZMod N) ∈ bohr (Finset.univ.image fun i => theta i u) (tau/4)
        then (1 : Real) else 0)-density) ≤
    (final.2^power/scale)^4*((bohr B' tau).card : Real)^2*((bohr S ((1/(8*Real.pi))/4)).card : Real)^2

theorem IsSingleCoherentProgression.density_controlled_graph {N d ell : Nat} [NeZero N] [Fact N.Prime]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    {P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N} {B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {x y : ZMod N → ZMod N}
    {t : Fin 4 → ZMod N} {color : ZMod N → Fin 4} {X : Finset (ZMod N)}
    {Q : Finset (Fin 4 → ZMod N)}
    (h : IsSingleCoherentProgression H T L delta kappa d r P B theta x y t color X Q)
    (hd : 0 < delta) (hk : 0 < kappa) (power : Nat) {scale : Real} (hscale : 0 < scale)
    (hN : singleCoherentGraphModulusBound delta kappa d r power scale ≤ N) :
    HasSingleCoherentGraph Q X B theta (fun u => shiftAnchorMap T L r x y (t (color u)+u))
      delta kappa d r power scale := by
  letI : NeZero singleCoherentGraphCells := ⟨ne_of_gt singleCoherentGraphCells_pos⟩
  letI : NeZero (singleCoherentGraphH d r) := ⟨ne_of_gt (singleCoherentGraphH_pos d r)⟩
  obtain ⟨Gamma,hG,hB,hell,hX,htheta,hmass,hfamily⟩ := h.regularity_input
  have hGrank : Gamma.card ≤ singleCoherentGraphInitialRank delta kappa d r := hG.trans (le_max_left _ _)
  have hBrank : B.card ≤ singleCoherentGraphInitialRank delta kappa d r := hB.trans (le_max_right _ _)
  have hN' := coherentUniformGraphModulusBound_spec power scale (singleCoherentGraphH d r)
    singleCoherentGraphCells (8*jointSelectionRank d r) (1/(8*Real.pi))
    (singleCoherentGraphInitialRank delta kappa d r) (singleProgressionDensity delta kappa d r) hB hell hN
  obtain ⟨s,hs,S,B',V,R,source,density,hprops,hBstate,hfinal,hden,hden1,hbox⟩ :=
    exists_coherent_density_controlled_graph Q X Gamma B theta
      (fun u => shiftAnchorMap T L r x y (t (color u)+u)) power
      (by positivity : (0 : Real) < 1/(8*Real.pi)) le_rfl
      (half_pos (jointSelectionRadius_pos d r)) (jointSelectionRadius_half_lt_quarter d r)
      (singleProgressionDensity_pos hd hk d r) hscale singleCoherentGraphCells_spec
      (singleCoherentGraphH_spec d r hell) (singleCoherentGraphInitialRank delta kappa d r)
      hGrank hBrank htheta hX hfamily hmass hN'
  exact ⟨Gamma,hGrank,s,hs.trans (Nat.sub_le _ _),S,B',V,R,source,density,
    hprops,hBstate,hfinal,hden,hden1,hbox⟩

end LeanProofs.GowersSzemeredi
