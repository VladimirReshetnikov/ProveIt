import GowersSzemeredi.Proofs16SingleCoherentBridgeParameters

/-! The original single anchor family supplies a genuine weak-transitivity
system, with a uniform threshold and all source witnesses preserved. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasSingleCoherentBridgeSystem {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (delta kappa : Real) (d : Nat) (r : Real) (depth power : Nat) (scale : Real) : Prop :=
  let sigma := jointSelectionRadius d r/2
  let H := coherentRadiusProfileCells sigma ell depth
  let m := coherentGraphFrequencyBound B.card ell
  let k := 4*(B.card+4*ell*ell+ell)
  let e := fun a : Nat × Real => coherentBridgeAccuracy H m k (a.2^power/scale)
  let initial := (singleCoherentGraphInitialRank delta kappa d r,singleProgressionDensity delta kappa d r)
  ∃ Gamma : Finset (ZMod N), Gamma.card ≤ initial.1 ∧
  ∃ s : Nat, s ≤ ell ∧
  let final := (coherentAdaptiveGraphState e H m singleCoherentGraphCells ell (1/(8*Real.pi)))^[s] initial
  let tau := sigma/(2 : Real)^s
  ∃ (S B' V : Finset (ZMod N)) (R : Finset (Fin 4 → ZMod N)) (source : ZMod N → ZMod N),
    IsCoherentFrequencyRefinement Q X Gamma B theta F (1/(8*Real.pi)) tau
      final.2 final.1 (B.card+4*s*ell) (4^s) S B' V R source ∧
    B'.card ≤ final.1 ∧ 0 < final.2 ∧
    DenseBohrGraphProfiles B' (bohr S ((1/(8*Real.pi))/4)) theta H m (e final) ∧
    CoherentBridgeSystem B' V theta (fun u => F (source u)) tau (final.2^power/scale) depth

theorem IsSingleCoherentProgression.bridge_system {N d ell : Nat} [NeZero N] [Fact N.Prime]
    {H : Finset (HigherArrangementParameter N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r : Real}
    {P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N} {B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {x y : ZMod N → ZMod N}
    {t : Fin 4 → ZMod N} {color : ZMod N → Fin 4} {X : Finset (ZMod N)}
    {Q : Finset (Fin 4 → ZMod N)}
    (h : IsSingleCoherentProgression H T L delta kappa d r P B theta x y t color X Q)
    (hd : 0 < delta) (hk : 0 < kappa) (depth power : Nat) {scale : Real} (hscale : 0 < scale)
    (hN : singleCoherentBridgeModulusBound delta kappa d r depth power scale ≤ N) :
    HasSingleCoherentBridgeSystem Q X B theta (fun u => shiftAnchorMap T L r x y (t (color u)+u))
      delta kappa d r depth power scale := by
  letI : NeZero singleCoherentGraphCells := ⟨ne_of_gt singleCoherentGraphCells_pos⟩
  obtain ⟨Gamma,hG,hB,hell,hX,htheta,hmass,hfamily⟩ := h.regularity_input
  have hGrank : Gamma.card ≤ singleCoherentGraphInitialRank delta kappa d r := hG.trans (le_max_left _ _)
  have hBrank : B.card ≤ singleCoherentGraphInitialRank delta kappa d r := hB.trans (le_max_right _ _)
  have hN' := singleCoherentBridgeModulusBound_spec delta kappa d r depth power scale hB hell hN
  obtain ⟨s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge⟩ :=
    exists_coherent_bridge_system Q X Gamma B theta
      (fun u => shiftAnchorMap T L r x y (t (color u)+u)) power depth
      (by positivity : (0 : Real) < 1/(8*Real.pi)) le_rfl
      (half_pos (jointSelectionRadius_pos d r)) (jointSelectionRadius_half_lt_quarter d r)
      (singleProgressionDensity_pos hd hk d r) hscale singleCoherentGraphCells_spec
      (singleCoherentGraphInitialRank delta kappa d r) hGrank hBrank htheta hX hfamily hmass hN'
  exact ⟨Gamma,hGrank,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge⟩

end LeanProofs.GowersSzemeredi
