import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeRightSide
import IPRADerivations.Analysis.Gamma.Names.PositiveAxis.GaussianNamedGammaPositiveLower
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# The Raabe right side at a certified positive regular real name

The logarithm uses the original positive logarithm on the positive
retiming of the input name. Freezing one actual rational sample gives
a uniform rate to the original rational Raabe right side, independent
of the frozen fraction's numerator and denominator.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeNamedRightSide

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedPositiveLateLogSource (retimedF retimedData)
open GaussianNamedRightHalfPlane (threshold)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData
local notation "L" => GaussianNamedPositiveLogarithm.nameF
local notation "ld" => GaussianNamedPositiveLogarithm.data
local notation "Diff" => GaussianNamedDifference.nameF
local notation "diffData" => GaussianNamedDifference.data

abbrev source (f : PR 2) (x M : PTm n) : Fm PTm n := GaussianNamedGammaPositiveLower.source f x M

abbrev logarithmF (f : PR 2) : PR 2 := L (retimedF f)

def logarithmData (x M : PTm n) : PTm n := ld (retimedData x M) (two*M)

def productF (f : PR 2) : PR 2 := multiplyF f (logarithmF f)

def productData (f : PR 2) (x M : PTm n) : PTm n :=
  multiplyData f (logarithmF f) x (logarithmData x M)

def primitiveF (f : PR 2) : PR 2 := Diff (productF f) f

def primitiveData (f : PR 2) (x M : PTm n) : PTm n := diffData (productData f x M) x

def nameF (f : PR 2) : PR 2 := addF (primitiveF f) C

def data (f : PR 2) (x M w : PTm n) : PTm n := addData (primitiveData f x M) (cd w)

def numerator (f : PR 2) (k x M : PTm n) : PTm n :=
  GaussianNamedPositiveLogarithm.numerator (retimedF f) k (retimedData x M)

def denominator (f : PR 2) (k x M : PTm n) : PTm n :=
  GaussianNamedPositiveLogarithm.denominator (retimedF f) k (retimedData x M)

def cost (f : PR 2) (x M : PTm n) : PTm n :=
  U (logarithmF f) (logarithmData x M)+U f x*(two*M)+one

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x M w : PTm n) :
    Syn.subst σ (data f x M w) = data f (Syn.subst σ x) (Syn.subst σ M) (Syn.subst σ w) := by
  simp [data,primitiveData,productData,logarithmData,two]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x M : PTm n) :
    Syn.subst σ (numerator f k x M) = numerator f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ M) := by
  simp [numerator,GaussianNamedPositiveLogarithm.numerator]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (k x M : PTm n) :
    Syn.subst σ (denominator f k x M) = denominator f (Syn.subst σ k) (Syn.subst σ x) (Syn.subst σ M) := by
  simp [denominator,GaussianNamedPositiveLogarithm.denominator]

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x M : PTm n) :
    Syn.subst σ (cost f x M) = cost f (Syn.subst σ x) (Syn.subst σ M) := by
  simp [cost,logarithmData,one,two]

private theorem positive_log_source (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source (retimedF f) (retimedData x M) (two*M) (U f x) :=
  GaussianNamedPositiveLateLogSource.positive_source f x M h.andE₁ h.andE₂

theorem frozen_domain (f : PR 2) (k x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (numerator f k x M) (denominator f k x M) (two*M) (U f x) :=
  GaussianNamedPositiveLogarithm.decoded_domain (retimedF f) k (retimedData x M) (two*M) (U f x)
    (positive_log_source f x M h)

theorem frozen_source (f : PR 2) (k x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (numerator f k x M) (denominator f k x M) :=
  (frozen_domain f k x M h).andE₁

theorem fraction_at (f : PR 2) (k x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] fraction (numerator f k x M) (denominator f k x M) ≐ ap2 f (k+threshold M) x :=
  (GaussianNamedPositiveLogarithm.decoded_value (retimedF f) k (retimedData x M) (two*M) (U f x)
    (positive_log_source f x M h)).eqTrans (GaussianNamedPositiveLateLogSource.sample_at f k x M)

theorem logarithm_regular (f : PR 2) (x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] pointCN (logarithmF f) (logarithmData x M) :=
  GaussianNamedPositiveLogarithm.name_regular (retimedF f) (retimedData x M) (two*M) (U f x)
    (positive_log_source f x M h)

theorem regular (f : PR 2) (x M w : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] pointCN (nameF f) (data f x M w) := by
  have hf := h.andE₁.andE₁
  have hl := logarithm_regular f x M h
  have product := multiply_fast f (logarithmF f) x (logarithmData x M) hf hl
  exact add_fast (primitiveF f) C (primitiveData f x M) (cd w)
    (GaussianNamedDifference.name_regular (productF f) f (productData f x M) x product hf)
    (GaussianStirlingConstant.name_regular w)

private theorem frozen_argument (f : PR 2) (k x M : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] independentRate f constantF x (fraction (numerator f k x M) (denominator f k x M)) one (unit k) := by
  let j := k+threshold M
  let q := ap2 f j x
  let r := fraction (numerator f k x M) (denominator f k x M)
  let D := unit k
  have hD := unit_positive (Γ := Γ) k
  have hf := h.andE₁.andE₁
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right k (threshold M))
  have late := GaussianSignedNameExponentialOrder.own_sample_rate f x j hf
  have hrate : Γ ⊢[PRAAx] independentRate f constantF x q one D :=
    GaussianNamedRateRadius.weaken f constantF x q one (unit j) one D (unit_positive j) hD
      (le_congr (one_mul D).eqSymm (one_mul (unit j)).eqSymm grow) late
  exact GaussianNamedRateTransport.transport f constantF f constantF x q x r one D hD hrate
    (cross_refl f x hf) (GaussianSignedNameExponentialOrder.constant_equal_cross r q (fraction_at f k x M h))

theorem frozen_rate (f : PR 2) (k x M w : PTm n) (h : Γ ⊢[PRAAx] source f x M) :
    Γ ⊢[PRAAx] independentRate (nameF f) GaussianRaabeRightSide.nameF (data f x M w)
      (GaussianRaabeRightSide.data (numerator f k x M) (denominator f k x M) w)
      (cost f x M) (unit k) := by
  let A := numerator f k x M
  let B := denominator f k x M
  let r := fraction A B
  let u := unit k
  let y := logarithmData x M
  let z := GaussianPositiveRationalLogarithm.data A B
  let P := GaussianRaabeRightSide.productF
  let e := GaussianRaabeRightSide.productData A B
  let T := U (logarithmF f) y
  let R := U f x
  let E := two*M
  let W := T*one+R*E
  have hu := unit_positive (Γ := Γ) k
  have hF := h.andE₁.andE₁
  have hL := logarithm_regular f x M h
  have hR := constant_regular (Γ := Γ) r
  have hZ := GaussianPositiveRationalLogarithm.name_regular A B (frozen_source f k x M h)
  have a := frozen_argument f k x M h
  have b : Γ ⊢[PRAAx] independentRate (logarithmF f) logF y z E u :=
    GaussianNamedPositiveLogarithm.original_frozen_rate (retimedF f) k (retimedData x M) E R
      (positive_log_source f x M h)
  have radius : Γ ⊢[PRAAx] GaussianRationalMetric.bounded r R one :=
    GaussianRationalReciprocal.bound_congr (fraction_at f k x M h).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianNameBounds.sample_bound f x (k+threshold M) hF)
  have product : Γ ⊢[PRAAx] independentRate (productF f) P (productData f x M) e W u :=
    GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator f (logarithmF f) constantF logF
      x y r z one E u T R hu hF hL hR hZ (GaussianNameBounds.all_samples_bounded _ _ hL)
      (GaussianEulerNamedPowerScalingPowerFrozen.constant_bound r R radius) a b
  have hP := multiply_fast f (logarithmF f) x y hF hL
  have hQ := multiply_fast constantF logF r z hR hZ
  have diff := GaussianNamedDifferenceRate.original_rate (productF f) f P constantF
    (productData f x M) x e r W u one u
    (.andI (.andI hu hu) (.andI (.andI hP hF) (.andI (.andI hQ hR) (.andI product a))))
  have core : Γ ⊢[PRAAx] independentRate (primitiveF f) GaussianRaabeRightSide.primitiveF
      (primitiveData f x M) (GaussianRaabeRightSide.primitiveData A B) (cost f x M) u :=
    GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product _ _ hu hu) hu
      (le_of_eq_add (d := zero) (by dsimp only [cost,W,T,R,E,GaussianNamedDifferenceRate.leadingNumerator,
        GaussianNamedDifferenceRate.leadingDenominator]; ipra_ring)) diff
  have sum := GaussianNamedAddRate.independent_rate (primitiveF f) C GaussianRaabeRightSide.primitiveF C
    (primitiveData f x M) (cd w) (GaussianRaabeRightSide.primitiveData A B) (cd w)
    (cost f x M) u zero one hu (le_refl one) core
    (GaussianNamedDifferenceRate.self_rate C (cd w) (GaussianStirlingConstant.name_regular w))
  exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring)
    (by unfold GaussianNamedRateComposition.leadingDenominator; ipra_ring) sum

theorem actual_named_Raabe_right_side_frozen_rate_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let k := var 0
       let x := var 1
       let M := var 2
       let w := var 3
       source f x M ⟶
         independentRate (nameF f) GaussianRaabeRightSide.nameF (data f x M w)
           (GaussianRaabeRightSide.data (numerator f k x M) (denominator f k x M) w)
           (cost f x M) (unit k)) :=
  closeUniv 4 (.impI (frozen_rate f _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRaabeNamedRightSide
