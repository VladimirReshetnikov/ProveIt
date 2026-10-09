import GowersSzemeredi.Proofs16SingleCoherentWordSystem
import GowersSzemeredi.Proofs16PopularCoherentBridge
import GowersSzemeredi.Proofs16RefinedSingleAgreement

/-! The bridge system and the popular original anchor witnesses belong to the same
single coherent family; later agreement transfer uses these exact witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasPopularCoherentWordSystem {N : Nat} [NeZero N]
    (C Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (popularity delta kappa : Real) (g d : Nat) (r : Real) (K : Nat) : Prop :=
  ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (B : Finset (ZMod N))
    (ell : Nat) (theta : Fin ell → ZMod N → ZMod N) (x y : ZMod N → ZMod N)
    (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (X : Finset (ZMod N))
    (Q : Finset (Fin 4 → ZMod N)),
    IsSingleCoherentProgression (popularSupportedHigherArrangements C popularity)
      (coreColumnSpectrum C Gamma T) (coreColumnMap C L) delta kappa (g+d) r
      P B theta x y t color X Q ∧
    (∀ u ∈ X, CoreAnchorAgreementAt C Gamma (B ∪ Finset.univ.image (fun i => theta i u))
      T L x y (t (color u)+u) r (jointSelectionRadius (g+d) r/2)
      (singleProgressionAgreementDensity popularity g d r)) ∧
    HasSingleCoherentWordSystem Q X B theta
      (fun u => shiftAnchorMap (coreColumnSpectrum C Gamma T) (coreColumnMap C L) r x y (t (color u)+u))
      delta kappa (g+d) r K

theorem HasPopularCoherentBridgeSystem.word_system {N g d K : Nat}
    [NeZero N] [Fact N.Prime]
    {C Gamma : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {popularity delta kappa r : Real}
    (h : HasPopularCoherentBridgeSystem C Gamma T L popularity delta kappa g d r 3 (coherentWordBridgePower K) (coherentWordBridgeScale K))
    (hN : 2 < N) :
    HasPopularCoherentWordSystem C Gamma T L popularity delta kappa g d r K := by
  obtain ⟨P,B,ell,theta,x,y,t,color,X,Q,hsingle,hagree,hbridge⟩ := h
  exact ⟨P,B,ell,theta,x,y,t,color,X,Q,hsingle,hagree,hbridge.word_system hN⟩

end LeanProofs.GowersSzemeredi
