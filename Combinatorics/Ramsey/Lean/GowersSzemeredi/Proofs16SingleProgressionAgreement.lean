import GowersSzemeredi.Proofs16SingleCoherentProgression

/-! Every selected point of the single family retains dense agreement
with the original core columns inside its actual unified Bohr domain. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def singleProgressionAgreementDensity (t : Real) (g d : Nat) (r : Real) : Real :=
  coreAnchorAgreementDensity t (16*jointSelectionRank (g+d) r) g d r
    (jointSelectionRadius (g+d) r/2)

theorem singleProgressionAgreementDensity_pos {t r : Real} (ht : 0 < t) (hr : 0 < r)
    (g d : Nat) : 0 < singleProgressionAgreementDensity t g d r := by
  apply coreAnchorAgreementDensity_pos ht hr
  have h := jointSelectionRadius_pos (g+d) r
  positivity

theorem IsSingleCoherentProgression.popular_agreement {N g d ell : Nat} [NeZero N]
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
    (hzero : ∀ v ∈ C, L v 0 = 0) (hrel : EvenColumnCoreRelations C Gamma T L r 4) :
    ∀ u ∈ X, CoreAnchorAgreementAt C Gamma (B ∪ Finset.univ.image (fun i => theta i u))
      T L x y (t (color u)+u) r (jointSelectionRadius (g+d) r/2)
      (singleProgressionAgreementDensity popularity g d r) := by
  obtain ⟨hPrank,hPproper,hPmass,hB,hell,htheta,ht,hXP,hX,hQ,hlocal,hcoherent⟩ := h
  intro u hu
  obtain ⟨a,ha,hmem,he⟩ := (hlocal u hu).2.2
  obtain ⟨hpopular,hx,hy⟩ := popular_shift_anchor_bases C x y a ha hmem (color u)
  rw [he] at hpopular hx hy
  have hD : (B ∪ Finset.univ.image (fun i => theta i u)).card ≤ 16*jointSelectionRank (g+d) r := by
    have hi : (Finset.univ.image (fun i => theta i u)).card ≤ ell :=
      Finset.card_image_le.trans (by simp)
    exact (Finset.card_union_le _ _).trans (by omega)
  constructor
  · exact coreAnchorAgreementDomain_uniform_density C Gamma
      (B ∪ Finset.univ.image (fun i => theta i u)) T x hr
      (half_pos (jointSelectionRadius_pos (g+d) r)) hD hG hT hx hpopular
  · exact coreAnchorAgreementDomain_agrees C Gamma
      (B ∪ Finset.univ.image (fun i => theta i u)) T L x y hr.le hrrho hL hzero hrel hx hy

def HasPopularSingleCoherentProgression {N : Nat} [NeZero N]
    (C Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (popularity delta kappa : Real) (g d : Nat) (r : Real) : Prop :=
  ∃ (P : OAI.Erdos3.BohrProgression.CyclicCenteredGAP N) (B : Finset (ZMod N))
    (ell : Nat) (theta : Fin ell → ZMod N → ZMod N) (x y : ZMod N → ZMod N)
    (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (X : Finset (ZMod N))
    (Q : Finset (Fin 4 → ZMod N)),
    IsSingleCoherentProgression (popularSupportedHigherArrangements C popularity)
      (coreColumnSpectrum C Gamma T) (coreColumnMap C L) delta kappa (g+d) r
      P B theta x y t color X Q ∧
    ∀ u ∈ X, CoreAnchorAgreementAt C Gamma (B ∪ Finset.univ.image (fun i => theta i u))
      T L x y (t (color u)+u) r (jointSelectionRadius (g+d) r/2)
      (singleProgressionAgreementDensity popularity g d r)

theorem HasSingleCoherentProgression.with_popular_agreement {N g d : Nat} [NeZero N]
    {C Gamma : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {L : ZMod N → ZMod N → ZMod N} {delta kappa r rho popularity : Real}
    (h : HasSingleCoherentProgression (popularSupportedHigherArrangements C popularity)
      (coreColumnSpectrum C Gamma T) (coreColumnMap C L) delta kappa (g+d) r)
    (hr : 0 < r) (hrrho : r ≤ rho) (hG : Gamma.card ≤ g) (hT : ∀ v ∈ C, (T v).card ≤ d)
    (hL : ∀ v ∈ C, IsFreimanLinearOn (bohr (T v) rho) (L v))
    (hzero : ∀ v ∈ C, L v 0 = 0) (hrel : EvenColumnCoreRelations C Gamma T L r 4) :
    HasPopularSingleCoherentProgression C Gamma T L popularity delta kappa g d r := by
  obtain ⟨P,B,ell,theta,x,y,t,color,X,Q,h⟩ := h
  exact ⟨P,B,ell,theta,x,y,t,color,X,Q,h,h.popular_agreement hr hrrho hG hT hL hzero hrel⟩

end LeanProofs.GowersSzemeredi
