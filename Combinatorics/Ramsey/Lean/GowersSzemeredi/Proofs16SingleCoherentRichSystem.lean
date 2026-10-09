import GowersSzemeredi.Proofs16CoherentRichPowerAccuracy
import GowersSzemeredi.Proofs16SingleCoherentBridge

/-! Preserve the actual refined witnesses while extracting the additively rich set
from the constructed single anchor family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasSingleCoherentRichSystem {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (delta kappa : Real) (d : Nat) (r : Real) (p : Nat) : Prop :=
  let depth := 3
  let power := 28+4*p
  let scale := coherentRichPowerScale
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
    HasCoherentRichSet V B' theta (fun u => F (source u)) tau final.2 (coherentRichSubsetDensity final.2 p)

theorem HasSingleCoherentBridgeSystem.rich_system {N ell : Nat} [NeZero N] [Fact N.Prime]
    {Q : Finset (Fin 4 → ZMod N)} {X B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {F : ZMod N → ZMod N → ZMod N}
    {delta kappa r : Real} {d p : Nat}
    (h : HasSingleCoherentBridgeSystem Q X B theta F delta kappa d r 3 (28+4*p) coherentRichPowerScale)
    (hN : 2 < N) :
    HasSingleCoherentRichSystem Q X B theta F delta kappa d r p := by
  obtain ⟨Gamma,hGamma,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge⟩ := h
  have hfamily := hprops.2.2.2.2.2.2.2.2.2.2.2
  have hmass := hprops.2.2.2.2.2.2.2.1
  have hscale := coherentRichPowerScale_pos
  have hk1 := hfamily.density_le_one hmass
  have hgraph := hbridge.rich_set (by positivity) le_rfl hfamily hfinal hmass
    (coherentRichPowerScale_pair_bound hfinal.le hk1 p) (coherentRichSubsetDensity_pos hfinal p)
    (coherentRichPowerScale_error_bound hfinal p) hN
  exact ⟨Gamma,hGamma,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge,hgraph⟩

end LeanProofs.GowersSzemeredi
