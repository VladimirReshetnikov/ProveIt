import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionOrdinaryImproper
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitSubstitutionRoundedEndpoints

/-!
# The actual ordinary quadrature panels exhaust the unit interval

The same numerator, width, and denominator supplied to the compact
unit-kernel name give two endpoints strictly inside the unit interval.
At any independently later original time cutoff, the endpoints are
within the requested dyadic radius of zero and one.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionOrdinaryEndpoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitSubstitutionOrdinaryImproper (source resolution laterSample)
open GaussianEulerUnitSubstitutionCompactName (stage)
open GaussianEulerUnitSubstitutionPanelSchedule (densityCount chartIndex latticeDenominator)
open GaussianEulerUnitSubstitutionLatticeGeometry (disk)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianEulerUnitDecayInput (clock)
open GaussianCoefficientNameBounds (unit)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qone)
open GaussianEuclideanDistanceName (fraction)
open RationalValueBounds (radius)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (p j A R : PTm n) : PTm n :=
  latticeDenominator (resolution p) R (width j A R) (etaDen j A R) (top j A R)
def leftNumerator (p j A R : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionPanelSchedule.left (resolution p) R one (width j A R) (etaDen j A R) (top j A R)
def widthNumerator (p j A R : PTm n) : PTm n :=
  GaussianEulerUnitSubstitutionPanelSchedule.width (resolution p) R one (width j A R) (etaDen j A R) (top j A R)
def rightNumerator (p j A R : PTm n) : PTm n := leftNumerator p j A R+widthNumerator p j A R

theorem quadrature_at (p j z R B A : PTm n) : Γ ⊢[PRAAx]
    laterSample p j z R B A ≐ ap2 GaussianEulerUnitKernelCompactName.nameF (resolution p)
      (GaussianEulerUnitKernelCompactName.data z R B (leftNumerator p j A R) (widthNumerator p j A R)
        (denominator p j A R) (disk (etaDen j A R) (top j A R))) :=
  .eqRefl _

def endpointBounds (p j A R : PTm n) : Fm PTm n :=
  (le one (leftNumerator p j A R) ⋏ lt (rightNumerator p j A R) (denominator p j A R)) ⋏
    (radius (fraction (leftNumerator p j A R) (denominator p j A R)) (fstT qzero) one (unit p) ⋏
      radius (fraction (rightNumerator p j A R) (denominator p j A R)) (fstT qone) one (unit p))

theorem later_endpoints (p j z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hj : Γ ⊢[PRAAx] le (resolution p) j) : Γ ⊢[PRAAx] endpointBounds p j A R := by
  let s := resolution p
  let C := width j A R
  let E := etaDen j A R
  let T := top j A R
  let N := densityCount s R C E T
  let k := chartIndex s R C E T
  let M := latticeDenominator s R C E T
  have original := GaussianEulerIntegralGammaIdentification.improper_source z R B A h
  have timeSource := GaussianEulerUnitSubstitutionImproperName.cutoff_source j z R B A original
  have panel := GaussianEulerUnitSubstitutionPanelSchedule.geometry_source s z R B one C E T timeSource
  have floor : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionRoundedEndpoints.source k N j A R M :=
    GaussianEulerUnitSubstitutionLatticeGeometry.cuts_source k N z R B one C E T M panel
  have laterQuery : Γ ⊢[PRAAx] le s (clock k E T) :=
    le_trans (GaussianEulerUnitSubstitutionPanelSchedule.chart_later s R C E T)
      (GaussianEulerUnitDecayInput.clock_later k E T)
  have laterUnit : Γ ⊢[PRAAx] le (unit (stage p)) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_add_right (stage p) (num 4))
  have hM : Γ ⊢[PRAAx] le (unit (stage p)) M :=
    le_trans laterUnit (GaussianEulerUnitSubstitutionPanelSchedule.floor_budget s R C E T)
  have htilt : Γ ⊢[PRAAx] le (two*N*unit (stage p)) (unit (clock k E T)) :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (two*N)) laterUnit)
      (GaussianEulerUnitSubstitutionPanelSchedule.tilt_budget s R C E T)
  have guards : Γ ⊢[PRAAx] GaussianEulerUnitSubstitutionRoundedEndpoints.dyadicSource p k N j A R M :=
    .andI floor (.andI original.andE₂.andE₁ (.andI hj (.andI laterQuery (.andI hM htilt))))
  exact .andI (GaussianEulerUnitSubstitutionRoundedEndpoints.native_endpoints k N one C E T M floor)
    (GaussianEulerUnitSubstitutionRoundedEndpoints.original_dyadic_endpoints p k N j A R M guards)

theorem canonical_endpoints (p z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    endpointBounds p (resolution p) A R :=
  later_endpoints p (resolution p) z R B A h (le_refl _)

theorem actual_ordinary_unit_panels_exhaust_interval_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 2) (var 3) (var 4) (var 5) ⋏ le (resolution (var 0)) (var 1)) ⟶
      endpointBounds (var 0) (var 1) (var 5) (var 3)) :=
  closeUniv 6 (.impI (later_endpoints _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionOrdinaryEndpoints
