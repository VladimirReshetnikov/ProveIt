import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLocationInput
import IPRADerivations.Analysis.Gamma.Digamma.GaussianGammaDigammaLocationResidual
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralUpperBound
import IPRADerivations.Analysis.Gamma.GaussianGammaHalfPlaneInputContinuity

/-!
# The original logarithmic Euler integral is small at the grid location

Use the uniform Gamma bound on [1,2] and the original identity
Gamma·digamma = the first logarithmic Euler integral. The native
normalized multiplication is evaluated at its own internal clock.
The bound on the product has a constant independent of the grid
numerator and denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegralUpperTransfer (paperConstant)
open GaussianGammaDigammaDyadicLocation (lower)
open GaussianGammaDigammaDyadicMesh (grid grid_positive grid_scale)
open GaussianGammaDigammaLocationInput (lower_bound upper_bound rational_source)
open GaussianGammaDigammaNative (derivativeData gamma_times_digamma)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiplyRaw multiply_at)
open GaussianNameEquivalence (cross_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianReconstructionRoots (distance_zero_iff norm_from_distance)
open GaussianStirlingGammaLogarithm (arg gamma_source gammaData)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "IF" => GaussianEulerLogarithmicImproperName.nameF
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

def gammaCap : PTm n := paperConstant one two+num 3
def derivativeBudget : PTm n := two+gammaCap*two

@[simp] theorem subst_derivativeBudget {k : ℕ} (σ : Fin n → PTm k) :
    Syn.subst σ (derivativeBudget : PTm n) = (derivativeBudget : PTm k) := by
  simp [derivativeBudget,gammaCap,two,one]

private theorem compact_source (k : PTm n) :
    Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source (arg (lower k)) two (grid k) one := by
  let a := lower k
  let b := grid k
  have h := upper_bound (Γ := Γ) k
  have disk : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (arg a) (two*b) :=
    le_congr (GaussianGammaGaussReference.scaled_one_norm a).eqSymm (.eqRefl _) (le_mul_mono h h)
  have edge : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.realLower (arg a) one b := by
    unfold GaussianEulerLowerPowerCoefficients.realLower
    apply zle_of_toZ (monus a b)
    have e := natEq (eq_add_of_le (lower_bound (Γ := Γ) k))
    simp only [arg,ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one]
    ipra_simps
    linear_combination -e
  exact .andI (.andI (le_refl one) (.andI (.andI (grid_positive k) disk) edge)) (by ipra_le 1)

theorem original_gamma_bounded (k q : PTm n) :
    Γ ⊢[PRAAx] bounded (ap2 gammaF q (gammaData (lower k) (grid k))) gammaCap one := by
  let a := lower k
  let b := grid k
  let U := unit q
  let C := paperConstant (one : PTm n) two
  have hU := unit_positive (Γ := Γ) q
  have native := gamma_source a b (rational_source (Γ := Γ) k)
  have fixed := GaussianGammaHalfPlaneInputContinuity.reciprocal_source (arg a) two b one (compact_source (Γ := Γ) k)
  have apart := GaussianGammaRadiusOverlap.original_Gamma_observation_overlap q q (arg a) a two b one b one one native fixed
  have uniform := GaussianEulerIntegralUpperBound.original_gamma_bound q (arg a) two b one (compact_source (Γ := Γ) k)
  have full := norm_from_distance _ _ _ _ _ _ (positive_product _ _ hU hU) hU apart uniform
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hU hU) hU) (le_refl one) _ full
  change Γ ⊢[PRAAx] le (((U+U)*U+(C*U+one)*(U*U))*one) ((C+num 3)*(U*U*U))
  ipra_le 3*𝔞(U)^2*sl hU

private theorem original_product_residual (k : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (multiplyF gammaF DF) k (multiplyData gammaF DF (gammaData (lower k) (grid k)) (dd (lower k) (grid k))))
      qzero (gammaCap*two) (unit k) := by
  let a := lower k
  let b := grid k
  let x := gammaData a b
  let y := dd a b
  let L := multiplyModulus gammaF DF x y
  let t := GaussianFastValueCut.exponent L k
  let G := ap2 gammaF t x
  let S := ap2 DF t y
  have hK := unit_positive (Γ := Γ) k
  have hT := unit_positive (Γ := Γ) t
  have later : Γ ⊢[PRAAx] le (unit k) (unit t) :=
    GaussianExponentialReference.unit_monotone (le_add_right k _)
  have pays : Γ ⊢[PRAAx] le (num 6*unit k) b := by
    refine le_congr (.eqRefl _) (grid_scale k).eqSymm ?_
    ipra_le 58*𝔞(unit k)
  have e := GaussianGammaDigammaLocationResidual.original_residual_at (Γ := Γ) k t
  have small := distance_radius_mono _ _ _ _ two (unit k) (positive_product _ _ (grid_positive k) hT) hK
    (by ipra_le 𝔞(unit t)*sl pays+𝔞(b)*sl later) e
  have sb : Γ ⊢[PRAAx] bounded S two (unit k) := (distance_zero_iff _ _ _ hK).iffMp small
  have gb : Γ ⊢[PRAAx] bounded G gammaCap one := original_gamma_bounded k t
  have product : Γ ⊢[PRAAx] bounded (multiplyRaw gammaF DF t x y) (gammaCap*two) (unit k) :=
    bound_congr (.eqRefl _) (.eqRefl _) (one_mul _) (bounded_product G S gammaCap one two (unit k) (le_refl one) hK gb sb)
  have recoded := (GaussianFastValueCut.recode_bound_iff _ _ _ hK).iffMpr product
  exact (distance_zero_iff _ _ _ hK).iffMpr
    (bound_congr (multiply_at gammaF DF x y k).eqSymm (.eqRefl _) (.eqRefl _) recoded)

theorem native_derivative_residual_at (k : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (ap2 IF k (derivativeData (lower k) (grid k))) qzero derivativeBudget (unit k) := by
  let a := lower k
  let b := grid k
  have hK := unit_positive (Γ := Γ) k
  have link := cross_at _ _ _ _ k k (gamma_times_digamma a b (rational_source (Γ := Γ) k))
  have reversed := distance_symmetric _ _ _ _ (positive_product _ _ hK hK) link
  have same := distance_radius_mono _ _ _ _ two (unit k) (positive_product _ _ hK hK) hK
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) reversed
  exact distance_triangle_same _ _ _ _ _ _ hK same (original_product_residual k)

theorem original_location_logarithmic_integral_residual_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (distanceBounded (ap2 IF (var 0) (derivativeData (lower (var 0)) (grid (var 0))))
        qzero derivativeBudget (unit (var 0))) :=
  closeUniv 1 (native_derivative_residual_at _)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationProduct
