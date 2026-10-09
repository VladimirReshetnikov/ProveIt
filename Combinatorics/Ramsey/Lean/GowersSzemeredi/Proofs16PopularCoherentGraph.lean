import GowersSzemeredi.Proofs16RefinedSingleAgreement

/-! The graph and the popular original anchor witnesses belong to the same
single coherent family; later agreement transfer uses these exact witnesses. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def HasPopularCoherentGraph {N : Nat} [NeZero N]
    (C Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (popularity delta kappa : Real) (g d : Nat) (r : Real)
    (power : Nat) (scale : Real) : Prop :=
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
    HasSingleCoherentGraph Q X B theta
      (fun u => shiftAnchorMap (coreColumnSpectrum C Gamma T) (coreColumnMap C L) r x y (t (color u)+u))
      delta kappa (g+d) r power scale

theorem HasPopularSingleCoherentProgression.density_controlled_graph {N g d : Nat}
    [NeZero N] [Fact N.Prime]
    {C Gamma : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {popularity delta kappa r : Real}
    (h : HasPopularSingleCoherentProgression C Gamma T L popularity delta kappa g d r)
    (hd : 0 < delta) (hk : 0 < kappa) (power : Nat) {scale : Real} (hscale : 0 < scale)
    (hN : singleCoherentGraphModulusBound delta kappa (g+d) r power scale ≤ N) :
    HasPopularCoherentGraph C Gamma T L popularity delta kappa g d r power scale := by
  obtain ⟨P,B,ell,theta,x,y,t,color,X,Q,hsingle,hagree⟩ := h
  exact ⟨P,B,ell,theta,x,y,t,color,X,Q,hsingle,hagree,
    hsingle.density_controlled_graph hd hk power hscale hN⟩

end LeanProofs.GowersSzemeredi
