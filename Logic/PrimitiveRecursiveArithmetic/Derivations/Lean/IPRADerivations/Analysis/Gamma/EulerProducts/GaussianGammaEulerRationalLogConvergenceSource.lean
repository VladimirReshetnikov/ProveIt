import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalLogMargin
import IPRADerivations.Analysis.Exponential.GaussianNamedPositiveLogarithmExponential
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Positive names for the finite Euler and original Gamma logarithms

Both inverse names have a common late positive margin. The original
logarithm applied to their real, retimed observations agrees with
the existing finite Euler logarithm and the original Gamma logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogConvergenceSource

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerInverseConvergence (coefficientNumerator coefficientDenominator)
open GaussianGammaEulerRationalLogMargin (margin margin_positive source cutoff_source cutoff_positive denominator_positive inverseData)
open GaussianGammaEulerReciprocalInverse (eulerF)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianGammaRealValues (axisF axis_cross axis_regular)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveLateLogSource (retimedF retimedData original_cross positive_source)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianRealNameExponentialInjectivity (axisSamples independent_radii_injective)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianStirlingGammaLogarithm (gammaData gammaRealF gammaMargin gamma_real_cross gamma_real_positive
  logGammaF logGammaData log_gamma_regular log_gamma_axis)
open GaussianStirlingLogDuplication (exponential_gamma)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "nameRadius" => GaussianNameBounds.U
local notation "RF" => GaussianGammaEulerRationalLog.nameF
local notation "rd" => GaussianGammaEulerRationalLog.data
local notation "L" => GaussianNamedPositiveLogarithm.nameF
local notation "ld" => GaussianNamedPositiveLogarithm.data

abbrev finiteInputF : PR 2 := retimedF (axisF eulerF)
abbrev nativeInputF : PR 2 := retimedF gammaRealF
def finiteInputData (N a b : PTm n) : PTm n := retimedData (inverseData N a b) margin
def nativeInputData (a b : PTm n) : PTm n := retimedData (gammaData a b) margin
def logMargin : PTm n := two*margin
def finiteRadius (N a b : PTm n) : PTm n := nameRadius (axisF eulerF) (inverseData N a b)
def nativeRadius (a b : PTm n) : PTm n := nameRadius gammaRealF (gammaData a b)
def finiteLogData (N a b : PTm n) : PTm n := ld (finiteInputData N a b) logMargin
def nativeLogData (a b : PTm n) : PTm n := ld (nativeInputData a b) logMargin

@[simp] theorem subst_finiteInputData {m : ℕ} (σ : Fin n → PTm m) (N a b : PTm n) :
    Syn.subst σ (finiteInputData N a b) = finiteInputData (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) :=
  by simp [finiteInputData,margin]
@[simp] theorem subst_nativeInputData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (nativeInputData a b) = nativeInputData (Syn.subst σ a) (Syn.subst σ b) :=
  by simp [nativeInputData,margin]

private theorem real_axis (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] axisSamples f x := by
  refine .allI ?_
  let X := Syn.shift x
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f X := by simpa [Fm.shift,Syn.shift,X] using h.shift
  simpa only [axisSamples,Syn.shift,X] using (real_sample_at f X (var 0) hs).andE₂

private theorem real_conjugation (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF f) f x x := by
  refine GaussianNameConjugation.equal_samples_cross _ _ _ _ (GaussianNameConjugation.regular f x h) h (.allI ?_)
  let X := Syn.shift x
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let z := ap2 f p X
  have hs : Δ ⊢[PRAAx] realSamples f X := by simpa [Fm.shift,Syn.shift,X,Δ] using hr.shift
  have zreal := real_sample_at f X p hs
  have e := RationalGaussianEmbedding.canonical_axis_roundtrip z zreal.andE₁ zreal.andE₂
  have fix := (GaussianRationalConjugation.point_congr e.eqSymm).eqTrans
    ((GaussianRationalConjugation.point_embed (fstT z)).eqTrans e)
  simpa only [GaussianNameConjugation.pointwiseEqual,Syn.shift,X,p,Δ,z] using
    (GaussianNameConjugation.sample_at f p X).eqTrans fix

private theorem real_exponential_conjugation (f : PR 2) (R x : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f R x) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNameConjugation.nameF (E f)) (E f)
      (GaussianRadiusExponentialName.data R x) (GaussianRadiusExponentialName.data R x) := by
  have c := GaussianNameConjugation.exponential_cross f R x h
  have same := GaussianRadiusExponentialName.cross_proper (GaussianNameConjugation.nameF f) f R x x
    (GaussianNameConjugation.exponential_input f R x h) h (real_conjugation f x h.andE₁ hr)
  exact cross_trans _ _ _ _ _ _ c same

theorem inverse_real_cross (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] crossEquivalent eulerF (axisF eulerF) (inverseData N a b) (inverseData N a b) := by
  let x := rd N a b
  let u := ed RF x
  let d := inverseData N a b
  have hN := cutoff_positive N a b h
  have reg := GaussianGammaEulerRationalLog.name_regular N a b hN h.andE₁.andE₁ h.andE₁.andE₂
  have ex : Γ ⊢[PRAAx] crossEquivalent (E RF) eulerF u d :=
    GaussianGammaEulerRationalLog.original_euler_inverse_cross N a b (cutoff_source N a b h).andE₂.andE₁
      h.andE₁.andE₁ h.andE₁.andE₂
  have c := GaussianNameConjugation.conjugate_cross eulerF (E RF) d u (cross_symm _ _ _ _ ex)
  have fix := real_exponential_conjugation RF (nameRadius RF x) x (exponential_input _ _ reg)
    (GaussianGammaEulerRationalLog.name_real N a b h.andE₁.andE₂)
  have g := cross_trans _ _ _ _ _ _ c (cross_trans _ _ _ _ _ _ fix ex)
  exact axis_cross _ _ (GaussianGammaEulerRationalLogMargin.inverse_source N a b h).andE₁ g

private theorem native_margin_order (p q a b : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] RationalValueBounds.upper
      (fstT (ap2 GaussianGammaCanonicalExponent.constantF p (marginPoint (margin : PTm n))))
      (fstT (ap2 gammaRealF q (gammaData a b))) (GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q)
      (GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q) := by
  let z := fstT (ap2 gammaRealF q (gammaData a b))
  let A := GaussianCoefficientNameBounds.unit p+GaussianCoefficientNameBounds.unit q
  let B := GaussianCoefficientNameBounds.unit p*GaussianCoefficientNameBounds.unit q
  have previous := GaussianNamedPositiveExponentialOrder.real_order_at GaussianGammaCanonicalExponent.constantF gammaRealF
    (marginPoint gammaMargin) (gammaData a b) p q (gamma_real_positive a b h).andE₂.andE₂
  have h18 : Γ ⊢[PRAAx] le one (gammaMargin : PTm n) := by unfold gammaMargin; ipra_le 17
  have h36 := margin_positive (Γ := Γ) (n := n)
  have e18 := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) p (marginPoint gammaMargin))).eqTrans
    (GaussianGammaEulerRationalLogMargin.margin_scalar gammaMargin h18)
  have e36 := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ) p (marginPoint margin))).eqTrans
    (GaussianGammaEulerRationalLogMargin.margin_scalar margin h36)
  let f := GaussianEuclideanDistanceName.fraction (one : PTm n)
  have old := RationalValueBounds.upper_congr e18 (.eqRefl z) (.eqRefl A) (.eqRefl B) previous
  have v : Γ ⊢[PRAAx] RationalArgmin.rationalLE (f margin) (f gammaMargin) := by
    apply RationalArithmetic.order_of_representations _ _ (ZT.ofNat one) (ZT.ofNat one) margin gammaMargin
      (GaussianEuclideanDistanceName.fraction_represents _ _ h36)
      (GaussianEuclideanDistanceName.fraction_represents _ _ h18) h36 h18
    apply zle_of_toZ (LeanProofs.IPRA.PTm.num 18)
    simp only [ZT.toZ_mul,ZT.toZ_ofNat,margin,gammaMargin]
    ipra_simps
    ring
  exact RationalValueBounds.upper_congr e36.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (RationalValueBounds.upper_order_left _ _ _ _ _ v old)

theorem native_margin_source (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source gammaRealF (gammaData a b) margin := by
  refine .andI (gamma_real_positive a b h).andE₁ (.andI margin_positive (.allI (.allI ?_)))
  let sh (z : PTm n) := Syn.shift (Syn.shift z)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianStirlingGammaLogarithm.source (sh a) (sh b) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [GaussianNamedRightHalfPlane.certificate,GaussianNamedPositiveExponentialOrder.realOrder,
    GaussianNamedRightHalfPlane.subst_marginPoint,margin,LeanProofs.IPRA.PTm.subst_num,
    GaussianStirlingGammaLogarithm.subst_gammaData,Syn.shift,sh] using
    native_margin_order (var 1) (var 0) (sh a) (sh b) hs

theorem finite_log_input (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source finiteInputF (finiteInputData N a b) logMargin (finiteRadius N a b) :=
  positive_source _ _ _ (GaussianGammaEulerRationalLogMargin.projected_inverse_source N a b h)
    (GaussianEulerVerticalProjection.projected_real_samples eulerF (inverseData N a b))

theorem native_log_input (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source nativeInputF (nativeInputData a b) logMargin (nativeRadius a b) :=
  positive_source _ _ _ (native_margin_source a b h)
    (GaussianEulerVerticalProjection.projected_real_samples gammaF (gammaData a b))

theorem finite_input_cross (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] crossEquivalent eulerF finiteInputF (inverseData N a b) (finiteInputData N a b) :=
  cross_trans _ _ _ _ _ _ (inverse_real_cross N a b h)
    (original_cross (axisF eulerF) (inverseData N a b) margin
      (GaussianGammaEulerRationalLogMargin.projected_inverse_source N a b h).andE₁)

theorem native_input_cross (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF nativeInputF (gammaData a b) (nativeInputData a b) :=
  cross_trans _ _ _ _ _ _ (gamma_real_cross a b h)
    (original_cross gammaRealF (gammaData a b) margin (gamma_real_positive a b h).andE₁)

theorem input_rate (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] independentRate finiteInputF nativeInputF (finiteInputData N a b) (nativeInputData a b)
      (coefficientNumerator a b) (coefficientDenominator a one N) :=
  GaussianNamedRateTransport.transport eulerF gammaF finiteInputF nativeInputF
    (inverseData N a b) (gammaData a b) (finiteInputData N a b) (nativeInputData a b) _ _
    (denominator_positive N a b h)
    (GaussianGammaEulerInverseConvergence.actual_rate _ _ _ _ _ _ (cutoff_source N a b h))
    (cross_symm _ _ _ _ (finite_input_cross N a b h))
    (cross_symm _ _ _ _ (native_input_cross a b h.andE₁))

private theorem recovery (f : PR 2) (x A B : PTm n) (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x A B) :
    Γ ⊢[PRAAx] crossEquivalent (E (L f)) f (ed (L f) (ld x A)) x := by
  have old := GaussianNamedPositiveLogarithm.exponential_input f x A B h
  have new := exponential_input (L f) (ld x A) (GaussianNamedPositiveLogarithm.name_regular f x A B h)
  have e := GaussianExponentialRadiusIndependence.same_input_cross (L f) _ _ (ld x A) new old
  exact cross_trans _ _ _ _ _ _ e (GaussianNamedPositiveLogarithmExponential.original_recovery f x A B h)

theorem finite_log_cross (N a b : PTm n) (h : Γ ⊢[PRAAx] source N a b) :
    Γ ⊢[PRAAx] crossEquivalent RF (L finiteInputF) (rd N a b) (finiteLogData N a b) := by
  let x := rd N a b
  let y := finiteLogData N a b
  let f := finiteInputF
  let z := finiteInputData N a b
  have hs := finite_log_input N a b h
  have fr := GaussianGammaEulerRationalLog.name_regular N a b (cutoff_positive N a b h) h.andE₁.andE₁ h.andE₁.andE₂
  have gr := GaussianNamedPositiveLogarithm.name_regular f z logMargin (finiteRadius N a b) hs
  have e₁ := GaussianGammaEulerRationalLog.original_euler_inverse_cross N a b (cutoff_source N a b h).andE₂.andE₁
    h.andE₁.andE₁ h.andE₁.andE₂
  have e₂ := finite_input_cross N a b h
  have e₃ := recovery f z logMargin (finiteRadius N a b) hs
  exact independent_radii_injective RF (L f) _ _ x y
    (exponential_input _ _ fr) (exponential_input _ _ gr)
    (real_axis RF x (GaussianGammaEulerRationalLog.name_real N a b h.andE₁.andE₂))
    (GaussianNamedPositiveLogarithm.real_samples f z logMargin)
    (cross_trans _ _ _ _ _ _ e₁ (cross_trans _ _ _ _ _ _ e₂ (cross_symm _ _ _ _ e₃)))

theorem native_log_cross (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent logGammaF (L nativeInputF) (logGammaData a b) (nativeLogData a b) := by
  let x := logGammaData a b
  let y := nativeLogData a b
  let f := nativeInputF
  let z := nativeInputData a b
  have hs := native_log_input a b h
  have fr := log_gamma_regular a b h
  have gr := GaussianNamedPositiveLogarithm.name_regular f z logMargin (nativeRadius a b) hs
  have e₁ := exponential_gamma a b h
  have e₂ := native_input_cross a b h
  have e₃ := recovery f z logMargin (nativeRadius a b) hs
  exact independent_radii_injective logGammaF (L f) _ _ x y
    (exponential_input _ _ fr) (exponential_input _ _ gr) (log_gamma_axis a b)
    (GaussianNamedPositiveLogarithm.real_samples f z logMargin)
    (cross_trans _ _ _ _ _ _ e₁ (cross_trans _ _ _ _ _ _ e₂ (cross_symm _ _ _ _ e₃)))

end LeanProofs.IPRA.Analysis.GaussianGammaEulerRationalLogConvergenceSource
