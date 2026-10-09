import GowersSzemeredi.Proofs16CoherentNestedWordFamily
import GowersSzemeredi.Proofs16CoherentNestedProfileScale
import GowersSzemeredi.Proofs16CoherentWordEndpointIdentity
import GowersSzemeredi.Proofs16SingleCoherentBridge

/-! Preserve the actual refined witnesses while extracting the bounded-length compatible word family
from the constructed single anchor family. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasSingleCoherentNestedSystem {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    (delta kappa : Real) (d : Nat) (r : Real) (K L : Nat) : Prop :=
  let depth := coherentNestedBridgeDepth K L
  let power := coherentNestedBridgePower K L
  let scale := coherentNestedBridgeScale K L
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
    HasCoherentNestedWordFamily V B' theta (fun u => F (source u)) tau final.2 K L ∧
    CoherentWordEndpointIdentities V B' theta (fun u => F (source u)) tau ∧
    CoherentWordEndpointIdentities V B' theta (fun u => F (source u)) (tau/1296) ∧
    3 ≤ coherentNestedProfileRadius tau K L*H

theorem HasSingleCoherentBridgeSystem.nested_system {N ell : Nat} [NeZero N] [Fact N.Prime]
    {Q : Finset (Fin 4 → ZMod N)} {X B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {F : ZMod N → ZMod N → ZMod N}
    {delta kappa r : Real} {d K L : Nat}
    (h : HasSingleCoherentBridgeSystem Q X B theta F delta kappa d r (coherentNestedBridgeDepth K L) (coherentNestedBridgePower K L) (coherentNestedBridgeScale K L))
    (hN : 2 < N) :
    HasSingleCoherentNestedSystem Q X B theta F delta kappa d r K L := by
  obtain ⟨Gamma,hGamma,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge⟩ := h
  have hfamily := hprops.2.2.2.2.2.2.2.2.2.2.2
  have hmass := hprops.2.2.2.2.2.2.2.1
  have htau : 0 < (jointSelectionRadius d r/2)/(2 : Real)^s := by
    have hp := jointSelectionRadius_pos d r
    positivity
  have hwords := hbridge.nested_word_family K L htau.le (coherentNestedBridgeDepth_ge_seven K L) hfamily hfinal hmass hN
  have htheta : ∀ i, IsFreimanLinearOn V (theta i) := by
    intro i
    apply ((hprops.2.2.2.2.1 i).1.isFreimanLinearOn (by decide)).mono
    exact hprops.2.2.2.2.2.1.trans (bohr_mono_radius _ (by
      have hp := Real.pi_pos
      have hr : (0 : Real) ≤ 1/(8*Real.pi) := by positivity
      linarith : (1/(8*Real.pi))/4 ≤ 1/(8*Real.pi)))
  have hids := coherent_word_endpoint_identities (B := B') (F := fun u => F (source u))
    (sigma := (jointSelectionRadius d r/2)/(2 : Real)^s)
    (by have hp := jointSelectionRadius_pos d r; positivity) htheta
  have hids2 := coherent_word_endpoint_identities (B := B') (F := fun u => F (source u))
    (sigma := ((jointSelectionRadius d r/2)/(2 : Real)^s)/1296) (by positivity) htheta
  have hcells := coherentNestedProfileRadius_cells (sigma := jointSelectionRadius d r/2) (by have hp := jointSelectionRadius_pos d r; positivity)
    ell K L s hs
  exact ⟨Gamma,hGamma,s,hs,S,B',V,R,source,hprops,hBstate,hfinal,hprofile,hbridge,hwords,hids,hids2,hcells⟩

end LeanProofs.GowersSzemeredi
