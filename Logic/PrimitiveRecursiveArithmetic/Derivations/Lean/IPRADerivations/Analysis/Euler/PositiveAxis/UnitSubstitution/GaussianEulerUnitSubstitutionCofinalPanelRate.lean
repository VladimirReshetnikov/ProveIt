import IPRADerivations.Analysis.Euler.PositiveAxis.UnitSubstitution.GaussianEulerUnitSubstitutionOrdinaryEndpoints
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalNativeProjection

/-!
# Independent observations of a fixed computed ordinary unit panel

Fix the actual cofinal panel chosen at index t, then read its original
compact name at any independently requested p. Its original observation
at resolution(t) is exactly the ordinary cofinal program's t-th sample.
Regularity and the checked Gamma equivalence retain the two independent
output errors, with leading eps_t + eps_resolution(t), or safely 2eps_t.
Native real projection preserves the same Gamma disk and margin source.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionCofinalPanelRate

open_ipra
open GaussianEulerUnitSubstitutionOrdinaryImproper (source resolution)
open GaussianEulerUnitSubstitutionOrdinaryEndpoints (leftNumerator widthNumerator denominator)
open GaussianEulerUnitKernelCompactName (nameF)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerVerticalNativeProjection (argument)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianEulerUnitSubstitutionLatticeGeometry (disk)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def panelData (t z R B A : PTm n) : PTm n := GaussianEulerUnitKernelCompactName.data z R B
  (leftNumerator t (resolution t) A R) (widthNumerator t (resolution t) A R) (denominator t (resolution t) A R)
  (disk (etaDen (resolution t) A R) (top (resolution t) A R))
def leadingNumerator (t : PTm n) : PTm n := unit t+unit (resolution t)
def leadingDenominator (t : PTm n) : PTm n := unit t*unit (resolution t)

ipra_subst panelData [leftNumerator, widthNumerator, denominator, width, etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst leadingNumerator
ipra_subst leadingDenominator

@[simp] theorem subst_original_gammaData {m : ℕ} (σ : Fin n → PTm m) (z R B A : PTm n) :
    Syn.subst σ (gammaData z R B A) = gammaData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) := by
  simp [gammaData,GaussianGammaReciprocalInverse.gammaHeight]

/-- The same original positive margin A and disk R certify the real
projected native numerator, with the denominator B unchanged. -/
theorem projected_gamma_source (z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    source (argument z) R B A :=
  .andI (GaussianEulerVerticalNativeProjection.lower_source z R B A h.andE₁) h.andE₂

theorem panel_source (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianEulerUnitKernelCompactName.source z R B (leftNumerator t (resolution t) A R)
      (widthNumerator t (resolution t) A R) (denominator t (resolution t) A R)
      (disk (etaDen (resolution t) A R) (top (resolution t) A R)) := by
  have original := GaussianEulerIntegralGammaIdentification.improper_source z R B A h
  have time := GaussianEulerUnitSubstitutionImproperName.cutoff_source (resolution t) z R B A original
  exact GaussianEulerUnitSubstitutionPanelSchedule.panel_source (resolution t) z R B one
    (width (resolution t) A R) (etaDen (resolution t) A R) (top (resolution t) A R) time

theorem panel_regular (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    pointCN nameF (panelData t z R B A) :=
  GaussianEulerUnitKernelCompactName.name_regular _ _ _ _ _ _ _ (panel_source t z R B A h)

/-- This is exact program readback, not an equality of limiting values. -/
theorem original_sample_readback (t z R B A : PTm n) : Γ ⊢[PRAAx]
    ap2 GaussianEulerUnitSubstitutionOrdinaryImproper.nameF t (GaussianEulerUnitSubstitutionOrdinaryImproper.data z R B A) ≐
      ap2 nameF (resolution t) (panelData t z R B A) :=
  (GaussianEulerUnitSubstitutionOrdinaryImproper.name_at t z R B A).eqTrans
    (GaussianEulerUnitSubstitutionOrdinaryEndpoints.quadrature_at t (resolution t) z R B A)

theorem original_observations (p q t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (panelData t z R B A)) (ap2 gammaF q (gammaData z R B A))
      (rateNumerator (leadingNumerator t) (leadingDenominator t) p q) (rateDenominator (leadingDenominator t) p q) := by
  have first := GaussianNameEquivalence.point_at nameF (panelData t z R B A) p (resolution t) (panel_regular t z R B A h)
  have last := distance_congr (original_sample_readback t z R B A) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNameEquivalence.cross_at _ _ _ _ t q (GaussianEulerUnitSubstitutionOrdinaryImproper.original_Gamma_cross z R B A h))
  have full := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive (resolution t)))
    (positive_product _ _ (unit_positive t) (unit_positive q)) first last
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator leadingNumerator leadingDenominator; ipra_ring)
    (by unfold rateDenominator leadingDenominator; ipra_ring) full

theorem original_rate (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    independentRate nameF gammaF (panelData t z R B A) (gammaData z R B A) (leadingNumerator t) (leadingDenominator t) := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) :=
    by simpa [Fm.shift,source,GaussianEulerUnitSubstitutionGamma.source,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,subst_panelData,subst_original_gammaData,
    subst_leadingNumerator,subst_leadingDenominator,Syn.shift,sh] using
    original_observations (var 1) (var 0) (sh t) (sh z) (sh R) (sh B) (sh A) hs

theorem resolution_later (t : PTm n) : Γ ⊢[PRAAx] le t (resolution t) :=
  le_trans (le_add_right _ _) (le_add_right _ _)

theorem original_safe_observations (p q t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (panelData t z R B A)) (ap2 gammaF q (gammaData z R B A))
      (rateNumerator two (unit t) p q) (rateDenominator (unit t) p q) := by
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (resolution_later t)
  have hD : Γ ⊢[PRAAx] le one (rateDenominator (leadingDenominator t) p q) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (unit_positive t) (unit_positive (resolution t))) (unit_positive p)) (unit_positive q)
  have hd : Γ ⊢[PRAAx] le one (rateDenominator (unit t) p q) :=
    positive_product _ _ (positive_product _ _ (unit_positive t) (unit_positive p)) (unit_positive q)
  exact distance_radius_mono _ _ _ _ _ _ hD hd
    (by unfold rateNumerator rateDenominator leadingNumerator leadingDenominator
        ipra_le (Groth.ι (Q.mk Γ (unit t))*Groth.ι (Q.mk Γ (unit p))^2*Groth.ι (Q.mk Γ (unit q))^2)*sl grow)
    (original_observations p q t z R B A h)

theorem original_safe_rate (t z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    independentRate nameF gammaF (panelData t z R B A) (gammaData z R B A) two (unit t) := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh A) :=
    by simpa [Fm.shift,source,GaussianEulerUnitSubstitutionGamma.source,Syn.shift,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,subst_panelData,subst_original_gammaData,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh,one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    original_safe_observations (var 1) (var 0) (sh t) (sh z) (sh R) (sh B) (sh A) hs

theorem actual_fixed_computed_unit_panel_original_Gamma_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶ independentRate nameF gammaF
      (panelData (var 0) (var 1) (var 2) (var 3) (var 4)) (gammaData (var 1) (var 2) (var 3) (var 4))
      (leadingNumerator (var 0)) (leadingDenominator (var 0))) :=
  closeUniv 5 (.impI (original_rate _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionCofinalPanelRate
