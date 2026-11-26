import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerPowerScalingImageQuadrature
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.ImageGrids.GaussianEulerPositivePowerChartCorrectedImage

/-!
# The weighted Euler sum at the literal corrected chart nodes

The corrected widths are retained. Every ordinary Euler row is
evaluated at the actual positive rational encoding of the corrected
point. The comparison to the original image sum pays only the
controlled displacement and the two requested sampling errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCorrectedQuadrature

open_ipra
open GaussianEulerPositivePowerChartCorrectedImage (input imageNumerator imageDenominator)
open GaussianEulerPositivePowerChartImage (query reciprocalMargin)
open GaussianEulerPositivePowerChart (majorant)
open GaussianEulerPositivePowerChartMesh (widthNumerator cellDenominator)
open GaussianEulerPositivePowerChartMeshJacobian (width)
open GaussianEulerPowerScalingImageQuadrature (payload imageBody imageSum image_body_at)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalFiniteSum (sum)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (k z R B e f d h Q S E T a C N : PTm n) : Fm PTm n :=
  GaussianEulerPowerChartFrozenKernel.parameter z R B e f ⋏ input k e f d h Q S E T a C N
def correctedCell (p k i z B e f d h Q S E T a C N : PTm n) : PTm n :=
  qmul (width k i e f d h Q S E T a C N)
    (ap2 GaussianEulerIntegrandName.nameF p (GaussianEulerIntegrandName.data (scaled z f) (B*e)
      (imageNumerator k i e f d h Q S E T a C N) (imageDenominator k i e f d h Q S E T a C N)))
def gain (R h Q S E T N : PTm n) : PTm n :=
  GaussianEulerCompactModulus.lipschitz R (reciprocalMargin h Q E T) (majorant Q S E T+one)*(two*N)
def numerator (p k R h Q S E T C N : PTm n) : PTm n :=
  widthNumerator k h Q S E T C N*(gain R h Q S E T N*unit p+two*unit (query k h Q E T))
def denominator (p k h Q E T N : PTm n) : PTm n :=
  cellDenominator k h Q E T N*(unit (query k h Q E T)*unit p)

ipra_subst source [GaussianEulerPowerChartFrozenKernel.parameter, scaled, ComplexLogarithmRemainder.scale, ComplexLogarithmRemainder.bounded]
ipra_subst correctedCell [scaled, ComplexLogarithmRemainder.scale]
ipra_subst numerator [gain, GaussianEulerCompactModulus.lipschitz, GaussianEulerExponentCompactBounds.radius, GaussianEulerExponentCompactBounds.factor, GaussianRadiusExponentialLipschitzRate.factor]
ipra_subst denominator

theorem original_cell (p k i z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded (GaussianEulerPowerScalingCell.imageCell p k i z B e f d h Q S E T a C N)
      (correctedCell p k i z B e f d h Q S E T a C N)
      (numerator p k R h Q S E T C N) (denominator p k h Q E T N) := by
  let w := width k i e f d h Q S E T a C N
  let U := unit (query k h Q E T)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive _
  have hl := le_trans (le_succ_self i) hi
  have hG := GaussianEulerPositivePowerChartImage.margin_positive h Q E T hs.andE₂.andE₁.andE₁.andE₂.andE₁.andE₂
  have hz : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (scaled z f) R (B*e) (reciprocalMargin h Q E T) :=
    .andI hs.andE₁.andE₁ (.andI hG hs.andE₁.andE₂)
  have rate := GaussianEulerPositivePowerChartCorrectedImage.original_Euler_rate k i (scaled z f) R (B*e) e f d h Q S E T a C N
    hs.andE₂ hl hz
  have near := GaussianNamedInverseRate.diagonal_rate _ _ _ _ (gain R h Q S E T N) U p hU rate
  have hD := positive_product _ _ hU (unit_positive p)
  have hw := GaussianEulerPowerScalingCell.corrected_width_bound k i e f d h Q S E T a C N hs.andE₂.andE₁ hi
  have hv : Γ ⊢[PRAAx] le one (cellDenominator k h Q E T N) := positive_product _ _
    (positive_product _ _ hs.andE₂.andE₁.andE₂.andE₁ hs.andE₂.andE₁.andE₂.andE₂.andE₂.andE₂) hU
  have raw := bounded_product _ _ _ _ _ _ hv hD hw (distance_symmetric _ _ _ _ hD near)
  exact bound_congr (GaussianRationalRoundedPower.multiplication_difference w _ _).eqSymm (.eqRefl _) (.eqRefl _) raw

private def fields (i x : PTm n) : Fin 16 → PTm n :=
  Fin.cases i (fun j => Foundations.BoundedFormulas.at1 (Foundations.BoundedSyntax.projections 15 j) x)
private def body : PTm 16 :=
  correctedCell (var 1) (var 2) (var 0) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)
    (var 9) (var 10) (var 11) (var 12) (var 13) (var 14) (var 15)
def correctedBody : PTm 2 := Syn.subst (fields (var 0) (var 1)) body
def correctedSum (p k z B e f d h Q S E T a C N : PTm n) : PTm n :=
  sum correctedBody N (payload p k z B e f d h Q S E T a C N)

theorem corrected_body_at (p k i z B e f d h Q S E T a C N : PTm n) :
    Γ ⊢[PRAAx] inst2 correctedBody i (payload p k z B e f d h Q S E T a C N) ≐ correctedCell p k i z B e f d h Q S E T a C N := by
  let args : Fin 15 → PTm n := ![p,k,z,B,e,f,d,h,Q,S,E,T,a,C,N]
  let P := Foundations.BoundedSyntax.pack args
  have eval : inst2 correctedBody i P = Syn.subst (fields i P) body := by
    simp only [inst2,correctedBody,Syn.subst_subst]
    congr 1
    funext j
    cases j using Fin.cases with
    | zero => simp [fields]
    | succ j =>
      simp only [fields,Fin.cases_succ,Foundations.BoundedFormulas.at1,Syn.subst_subst]
      congr 1
      funext l
      fin_cases l
      rfl
  have decode : Syn.subst (Fin.cases i args) body = correctedCell p k i z B e f d h Q S E T a C N := by
    simp only [body,subst_correctedCell,Syn.subst_var]
    rfl
  have equality : Γ ⊢[PRAAx] Syn.subst (fields i P) body ≐ Syn.subst (Fin.cases i args) body := by
    refine Prf.eqCongr body (fun j => ?_)
    cases j using Fin.cases with
    | zero => exact .eqRefl _
    | succ j => exact Foundations.BoundedSyntax.projections_pack args j
  change Γ ⊢[PRAAx] inst2 correctedBody i P ≐ correctedCell p k i z B e f d h Q S E T a C N
  rw [eval,←decode]
  exact equality

theorem original_quadrature_to_corrected (p k z R B e f d h Q S E T a C N : PTm n)
    (hs : Γ ⊢[PRAAx] source k z R B e f d h Q S E T a C N) :
    Γ ⊢[PRAAx] distanceBounded (imageSum p k z B e f d h Q S E T a C N) (correctedSum p k z B e f d h Q S E T a C N)
      (N*numerator p k R h Q S E T C N) (denominator p k h Q E T N) := by
  let x := payload p k z B e f d h Q S E T a C N
  have hU := unit_positive (Γ := Γ) (query k h Q E T)
  have hD : Γ ⊢[PRAAx] le one (denominator p k h Q E T N) := positive_product _ _
    (positive_product _ _ (positive_product _ _ hs.andE₂.andE₁.andE₂.andE₁ hs.andE₂.andE₁.andE₂.andE₂.andE₂.andE₂) hU)
    (positive_product _ _ hU (unit_positive p))
  refine sum_distance imageBody correctedBody N x x _ _ hD (.allI (.impI ?_))
  let sh (t : PTm n) := Syn.shift t
  have ss : Γ.map Fm.shift ⊢[PRAAx] source (sh k) (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S)
      (sh E) (sh T) (sh a) (sh C) (sh N) := by simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift
  simp only [x,Syn.shift,GaussianEulerPowerScalingImageQuadrature.subst_payload,subst_numerator,subst_denominator]
  exact distance_congr (image_body_at (sh p) (sh k) (var 0) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h)
      (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)).eqSymm
    (corrected_body_at (sh p) (sh k) (var 0) (sh z) (sh B) (sh e) (sh f) (sh d) (sh h)
      (sh Q) (sh S) (sh E) (sh T) (sh a) (sh C) (sh N)).eqSymm (.eqRefl _) (.eqRefl _)
    (original_cell (sh p) (sh k) (var 0) (sh z) (sh R) (sh B) (sh e) (sh f) (sh d) (sh h) (sh Q) (sh S)
      (sh E) (sh T) (sh a) (sh C) (sh N) ss.wk Prf.hyp0)

theorem actual_original_corrected_power_scaling_quadrature_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 16
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
      (var 11) (var 12) (var 13) (var 14) (var 15) ⟶
      distanceBounded (imageSum (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 13) (var 14) (var 15))
      (correctedSum (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
        (var 10) (var 11) (var 12) (var 13) (var 14) (var 15))
      ((var 15)*numerator (var 0) (var 1) (var 3) (var 8) (var 9) (var 10) (var 11) (var 12) (var 14) (var 15))
      (denominator (var 0) (var 1) (var 8) (var 9) (var 11) (var 12) (var 15))) :=
  closeUniv 16 (.impI (original_quadrature_to_corrected _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerScalingCorrectedQuadrature
