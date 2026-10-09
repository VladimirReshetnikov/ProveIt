import GowersSzemeredi.Proofs16CoherentRobustGraph
import GowersSzemeredi.Proofs16SingleCoherentBridge

/-! Preserve the actual refined witnesses while extracting the robust graph
from the constructed single anchor family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasSingleCoherentRobustSystem {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (delta kappa : Real) (d : Nat) (r : Real)  : Prop :=
  let depth := 1
  let power := 2
  let scale : Real := 256
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
    CoherentBridgeSystem B' V theta (fun u => F (source u)) tau (final.2^power/scale) depth ∧
    HasCoherentRobustGraph V B' theta (fun u => F (source u)) tau final.2

theorem HasSingleCoherentBridgeSystem.robust_graph {N ell : Nat} [NeZero N] [Fact N.Prime]
    {Q : Finset (Fin 4 → ZMod N)} {X B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {F : ZMod N → ZMod N → ZMod N}
    {delta kappa r : Real} {d : Nat}
    (h : HasSingleCoherentBridgeSystem Q X B theta F delta kappa d r 1 2 256) (hN : 2 < N) :
    HasSingleCoherentRobustSystem Q X B theta F delta kappa d r := by
  obtain ⟨Gamma,hGamma,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge⟩ := h
  have hfamily := hprops.2.2.2.2.2.2.2.2.2.2.2
  have hmass := hprops.2.2.2.2.2.2.2.1
  have hgraph := hbridge.robust_graph (by positivity) le_rfl hfamily hfinal hmass le_rfl hN
  exact ⟨Gamma,hGamma,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge,hgraph⟩

end LeanProofs.GowersSzemeredi
