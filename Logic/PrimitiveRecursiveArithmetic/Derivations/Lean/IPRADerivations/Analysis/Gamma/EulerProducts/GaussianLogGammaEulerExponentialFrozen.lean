import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerExponentialLimit
import IPRADerivations.Analysis.Gamma.Names.GaussianNamedGammaLateInput
import IPRADerivations.Analysis.Names.GaussianNamedRightHalfPlaneSigned
import IPRADerivations.Analysis.Gamma.GaussianGammaRadiusOverlap

/-!
# The rational exponential identity at a late original Gamma observation

At a shared input clock, the signed chart and the original Gamma freeze
decode the same observation. Native value properness and certificate
overlap then compare the original programs with their respective radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFrozen

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaInputProperness (gamma_source_equal original_Gamma_proper)
open GaussianGammaRadiusOverlap (original_Gamma_overlap)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianLogGammaEulerCofinal (canonicalData)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius
  (radius radius_positive source_of_right_half_plane)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedRightHalfPlaneSigned (realNumerator imagNumerator denominator sign native_value)
open GaussianRationalL1 (rawGaussian)
open GaussianRadiusExponentialName (input)
open GaussianRootAlgebra (equal_symm)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => GaussianLogGammaEulerCofinal.nameF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "expData" => GaussianRadiusExponentialName.data
local notation "signedSource" => GaussianRightHalfPlaneLogarithm.source
local notation "gammaSource" => GaussianGammaReciprocalInverse.source

def logData (q : PTm n) : PTm n :=
  canonicalData (realNumerator q) (imagNumerator q) (denominator q) (sign q)

@[simp] theorem subst_logData {m : ℕ} (σ : Fin n → PTm m) (q : PTm n) :
    Syn.subst σ (logData q) = logData (Syn.subst σ q) := by simp [logData]

private theorem signed_gamma_source (A B D neg : PTm n) (h : Γ ⊢[PRAAx] signedSource A D neg) :
    Γ ⊢[PRAAx] gammaSource (native A B neg) (radius A B) D one D := by
  have hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (native A B neg) (radius A B) D :=
    .andI (radius_positive A B D neg h) (.andI h.andE₂ (source_of_right_half_plane A B D neg h).andE₂)
  have margin : Γ ⊢[PRAAx] GaussianGammaRightHalfPlane.realMargin (native A B neg) D D := by
    apply zle_of_toZ (D*monus A one)
    have e := natEq (eq_add_of_le h.andE₁.andE₁)
    simp only [native, ComplexLogarithmRemainder.eval_re_code, ZT.toZ_mul, ZT.toZ_ofNat]
    ipra_simps
    linear_combination -𝔞(D)*e
  exact GaussianGammaRightHalfPlane.original_right_half_plane_source _ _ _ _ hs h.andE₂ margin

theorem signed_equivalent (q R K W : PTm n)
    (h : Γ ⊢[PRAAx] signedSource (realNumerator q) (denominator q) (sign q))
    (hGamma : Γ ⊢[PRAAx] gammaSource (rawGaussian q) R (denominator q) one K)
    (hExp : Γ ⊢[PRAAx] input F W (logData q)) :
    Γ ⊢[PRAAx] crossEquivalent (Exp F) gammaF (expData W (logData q))
      (gammaData (rawGaussian q) R (denominator q) K) := by
  let A := realNumerator q
  let B := imagNumerator q
  let D := denominator q
  let neg := sign q
  let z := native A B neg
  let S := radius A B
  let L := GaussianLogGammaEulerExponentialLimit.disk A B D neg
  let x := logData q
  have reg := GaussianLogGammaEulerCofinal.canonical_regular A B D neg h
  have oldInput : Γ ⊢[PRAAx] input F L x :=
    GaussianExponentialRadiusIndependence.input_widen F _ L x
      (GaussianGammaFiniteApproximantName.exponential_input F x reg) (le_add_right _ _)
  have reindex := GaussianExponentialRadiusIndependence.same_input_cross F W L x hExp oldInput
  have rational := GaussianLogGammaEulerExponentialLimit.gamma_equivalent A B D neg h
  have eqNative := equal_symm (native_value q h.andE₁.andE₁)
  have rawOnSigned := gamma_source_equal (rawGaussian q) z R D one K hGamma eqNative
  have overlap := original_Gamma_overlap z S R D one D one K (signed_gamma_source A B D neg h) rawOnSigned
  have original := original_Gamma_proper (rawGaussian q) z R D one K hGamma eqNative
  exact cross_trans _ _ _ _ _ _ reindex
    (cross_trans _ _ _ _ _ _ rational
      (cross_trans _ _ _ _ _ _ overlap (cross_symm _ _ _ _ original)))

theorem frozen_equivalent (f : PR 2) (s k x M W : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedGammaLateInput.input f s k x M)
    (hExp : Γ ⊢[PRAAx] input F W (logData (ap2 f k x))) :
    Γ ⊢[PRAAx] crossEquivalent (Exp F) gammaF (expData W (logData (ap2 f k x)))
      (GaussianNamedGammaLateInput.encodedData f k x M) := by
  have q := GaussianNamedRightHalfPlaneSigned.actual_late f x M k h.andE₁ h.andE₂.andE₁
  have g := GaussianNamedGammaLateInput.encoded_source f s k x M h
  exact signed_equivalent (ap2 f k x) (GaussianNamedRightHalfPlane.radius f x) (two*M) W q.andE₁.andE₁
    (GaussianGammaHalfPlaneInputContinuity.reciprocal_source _ _ _ _ g) hExp

theorem actual_frozen_rational_log_Gamma_exponentiates_to_original_Gamma_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (GaussianNamedGammaLateInput.input f (var 0) (var 1) (var 2) (var 3) ⟶
        input F (var 4) (logData (ap2 f (var 1) (var 2))) ⟶
        crossEquivalent (Exp F) gammaF (expData (var 4) (logData (ap2 f (var 1) (var 2))))
          (GaussianNamedGammaLateInput.encodedData f (var 1) (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (frozen_equivalent f _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialFrozen
