import GowersSzemeredi.Proofs16SingleCoherentGraph
import GowersSzemeredi.Proofs16SingleProgressionAgreement

/-! Source witnesses transfer agreement with the original columns onto
the actual final Bohr domains, with a fresh explicit density estimate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem IsSingleCoherentProgression.refined_popular_agreement {N g d ell : Nat} [NeZero N]
    {C Gamma : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r rho popularity : Real}
    {P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N} {B : Finset (ZMod N)}
    {theta : Fin ell → ZMod N → ZMod N} {x y : ZMod N → ZMod N}
    {t : Fin 4 → ZMod N} {color : ZMod N → Fin 4} {X : Finset (ZMod N)}
    {Q : Finset (Fin 4 → ZMod N)}
    (h : IsSingleCoherentProgression (popularSupportedHigherArrangements C popularity)
      (coreColumnSpectrum C Gamma T) (coreColumnMap C L) delta kappa (g+d) r
      P B theta x y t color X Q)
    (hr : 0 < r) (hrrho : r ≤ rho) (hG : Gamma.card ≤ g) (hT : ∀ v ∈ C, (T v).card ≤ d)
    (hL : ∀ v ∈ C, IsFreimanLinearOn (bohr (T v) rho) (L v))
    (hzero : ∀ v ∈ C, L v 0 = 0) (hrel : EvenColumnCoreRelations C Gamma T L r 4)
    {base S B' V : Finset (ZMod N)} {R : Finset (Fin 4 → ZMod N)} {source : ZMod N → ZMod N}
    {rho' tau retained : Real} {rankBound fixedBound offsetBound : Nat} (htau : 0 < tau)
    (href : IsCoherentFrequencyRefinement Q X base B theta
      (fun u => shiftAnchorMap (coreColumnSpectrum C Gamma T) (coreColumnMap C L) r x y (t (color u)+u))
      rho' tau retained rankBound fixedBound offsetBound S B' V R source) :
    ∀ u ∈ V, CoreAnchorAgreementAt C Gamma (B' ∪ Finset.univ.image (fun i => theta i u))
      T L x y (t (color (source u))+source u) r tau
      (coreAnchorAgreementDensity popularity (fixedBound+ell) g d r tau) := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,hlocal,_⟩ := h
  obtain ⟨_,_,_,hB',_,_,_,_,_,hsource,_,_⟩ := href
  intro u hu
  obtain ⟨a,ha,hmem,he⟩ := (hlocal (source u) (hsource u hu)).2.2
  obtain ⟨hpopular,hx,hy⟩ := popular_shift_anchor_bases C x y a ha hmem (color (source u))
  rw [he] at hpopular hx hy
  have hD : (B' ∪ Finset.univ.image (fun i => theta i u)).card ≤ fixedBound+ell := by
    have hi : (Finset.univ.image (fun i => theta i u)).card ≤ ell :=
      Finset.card_image_le.trans (by simp)
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hB' hi)
  constructor
  · exact coreAnchorAgreementDomain_uniform_density C Gamma
      (B' ∪ Finset.univ.image (fun i => theta i u)) T x hr htau hD hG hT hx hpopular
  · exact coreAnchorAgreementDomain_agrees C Gamma
      (B' ∪ Finset.univ.image (fun i => theta i u)) T L x y hr.le hrrho hL hzero hrel hx hy

end LeanProofs.GowersSzemeredi
