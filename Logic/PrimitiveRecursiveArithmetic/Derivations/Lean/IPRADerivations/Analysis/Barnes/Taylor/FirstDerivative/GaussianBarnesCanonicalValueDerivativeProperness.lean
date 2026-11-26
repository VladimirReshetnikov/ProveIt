import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeStep
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalHeadDerivativeFractionProperness
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalPrefactorDerivativeProperness
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalTailDerivativeFractionProperness

/-!
# The original Barnes derivative on equivalent rational arguments

On one fixed certified disk, the actual finite and infinite derivative
factors respect equivalent Gaussian fractions. The divided differences
can therefore be compared with a single derivative name even when each
native step is evaluated in a finer rational encoding.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivativeProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalDerivativeStep (nativeBase nativeDenominator)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalValueDerivative (nameF data quotientF quotientData numerator denominator)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)
open ComplexLogarithmRemainder (oneCode bounded_mono)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Dprod" => GaussianNamedNativeProductDerivativeRate.derivativeF
local notation "dprod" => GaussianNamedNativeProductDerivativeRate.derivativeData
local notation "DI" => GaussianBarnesCanonicalPrefixDerivative.derivativeF
local notation "di" => GaussianBarnesCanonicalPrefixDerivative.derivativeData
local notation "I" => GaussianBarnesCanonicalValue.prefixF
local notation "id" => GaussianBarnesCanonicalValue.prefixData
local notation "H" => GaussianBarnesCanonicalHead.nameF
local notation "hd" => GaussianBarnesCanonicalHead.headData
local notation "DH" => GaussianBarnesCanonicalHeadDerivativeJoin.derivativeF
local notation "dh" => GaussianBarnesCanonicalHeadDerivativeJoin.derivativeData
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "pd" => GaussianBarnesCanonicalPrefactor.data
local notation "DP" => GaussianBarnesCanonicalPrefactorDerivative.derivativeF
local notation "dp" => GaussianBarnesCanonicalPrefactorDerivative.derivativeData
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "DT" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeF
local notation "dt" => GaussianBarnesCanonicalTailExponentialDerivative.derivativeData

private theorem same_data (F : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] pointCN F x)
    (eq : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] crossEquivalent F F x y :=
  GaussianGammaCompactCutoffAlignment.cross_data_congr F F x x x y (.eqRefl _) eq (cross_refl F x h)

private theorem product_derivative_cross (F G J K : PR 2) (x x' y y' u u' v v' : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN F x) (hx' : Γ ⊢[PRAAx] pointCN F x')
    (hy : Γ ⊢[PRAAx] pointCN G y) (hy' : Γ ⊢[PRAAx] pointCN G y')
    (hu : Γ ⊢[PRAAx] pointCN J u) (hu' : Γ ⊢[PRAAx] pointCN J u')
    (hv : Γ ⊢[PRAAx] pointCN K v) (hv' : Γ ⊢[PRAAx] pointCN K v')
    (ex : Γ ⊢[PRAAx] crossEquivalent F F x x') (ey : Γ ⊢[PRAAx] crossEquivalent G G y y')
    (eu : Γ ⊢[PRAAx] crossEquivalent J J u u') (ev : Γ ⊢[PRAAx] crossEquivalent K K v v') :
    Γ ⊢[PRAAx] crossEquivalent (Dprod F G J K) (Dprod F G J K)
      (dprod F G J K x y u v) (dprod F G J K x' y' u' v') :=
  GaussianNamedGammaHalfShift.add_cross _ _ _ _ _ _ _ _
    (multiply_fast K F v x hv hx) (multiply_fast K F v' x' hv' hx')
    (multiply_fast G J y u hy hu) (multiply_fast G J y' u' hy' hu')
    (GaussianGammaAdjacentCutoff.multiply_cross K K F F v v' x x' hv hv' hx hx' ev ex)
    (GaussianGammaAdjacentCutoff.multiply_cross G G J J y y' u u' hy hy' hu hu' ey eu)

theorem head_proper (z w B C N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hC : Γ ⊢[PRAAx] le one C)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx] crossEquivalent DH DH (dh z B N) (dh w C N) := by
  let F := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponentialF
  let F' := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.derivativeF
  let pow : PTm n → PTm n → PTm n → PTm n := GaussianBarnesCanonicalBaseProductShift.powerProduct
  let slope : PTm n → PTm n → PTm n → PTm n := GaussianBarnesCanonicalHeadPolynomialDerivative.powerSlope
  let exp : PTm n → PTm n → PTm n → PTm n := GaussianBarnesCanonicalHeadExponentialFactors.exponentData
  let exp' : PTm n → PTm n → PTm n → PTm n := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.derivativeData
  have p := GaussianBarnesCanonicalHeadDerivativeFractionProperness.original_power_equal z w B C N hB hC eq
  have q := GaussianBarnesCanonicalHeadDerivativeFractionProperness.power_slope_equal z w B C N eq
  have r := GaussianBarnesCanonicalHeadDerivativeFractionProperness.exponent_data_equal z w B C N hB hC eq
  have s := GaussianBarnesCanonicalHeadDerivativeFractionProperness.correction_slope_equal z w B C N eq
  have rn := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponential_regular (Γ := Γ) z B N
  have rm := GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.exponential_regular (Γ := Γ) w C N
  have r' := same_data F (exp z B N) (exp w C N) rn r
  have d' := GaussianGammaAdjacentCutoff.multiply_cross F F constantF constantF _ _ _ _ rn rm
    (constant_regular _) (constant_regular _) r' (same_data constantF _ _ (constant_regular _) s)
  exact product_derivative_cross constantF F constantF F' (pow z B N) (pow w C N) (exp z B N) (exp w C N)
    (slope z B N) (slope w C N) (exp' z B N) (exp' w C N)
    (constant_regular _) (constant_regular _) rn rm (constant_regular _) (constant_regular _)
    (GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.derivative_regular z B N)
    (GaussianBarnesCanonicalHeadCorrectionExponentialDerivative.derivative_regular w C N)
    (same_data constantF _ _ (constant_regular _) p) r' (same_data constantF _ _ (constant_regular _) q) d'

theorem prefix_proper (z w R B C : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R C)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx] crossEquivalent DI DI (di z R B) (di w R C) := by
  let N := initial R
  exact product_derivative_cross H P DH DP (hd z R B N) (hd w R C N) (pd z B) (pd w C) (dh z B N) (dh w C N) (dp z B) (dp w C)
    (GaussianBarnesCanonicalHead.regular z R B zero N hz) (GaussianBarnesCanonicalHead.regular w R C zero N hw)
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalPrefactor.regular w C)
    (GaussianBarnesCanonicalHeadDerivativeJoin.regular z B N) (GaussianBarnesCanonicalHeadDerivativeJoin.regular w C N)
    (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular z B) (GaussianBarnesCanonicalPrefactorDerivative.derivative_regular w C)
    (GaussianBarnesCanonicalFiniteProperness.segment_cross z w R R B C zero N hz hw eq)
    (GaussianBarnesCanonicalFiniteProperness.prefactor_cross z w B C eq)
    (head_proper z w B C N hz.andE₁ hw.andE₁ eq)
    (GaussianBarnesCanonicalPrefactorDerivativeProperness.derivative_cross z w B C eq)

theorem proper (z w R B C : PTm n) (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source w R C)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx] crossEquivalent nameF nameF (data z R B) (data w R C) := by
  let N := initial R
  have hp := GaussianBarnesCanonicalFiniteProperness.prefactor_cross z w B C eq
  have hh := GaussianBarnesCanonicalFiniteProperness.segment_cross z w R R B C zero N hz hw eq
  have pre := GaussianGammaAdjacentCutoff.multiply_cross P P H H (pd z B) (pd w C) (hd z R B N) (hd w R C N)
    (GaussianBarnesCanonicalPrefactor.regular z B) (GaussianBarnesCanonicalPrefactor.regular w C)
    (GaussianBarnesCanonicalHead.regular z R B zero N hz) (GaussianBarnesCanonicalHead.regular w R C zero N hw) hp hh
  exact product_derivative_cross I T DI DT (id z R B) (id w R C) (td z R B) (td w R C)
    (di z R B) (di w R C) (dt z R B) (dt w R C)
    (GaussianBarnesCanonicalValue.prefix_regular z R B hz) (GaussianBarnesCanonicalValue.prefix_regular w R C hw)
    (GaussianBarnesCanonicalTailExponential.regular z R B hz) (GaussianBarnesCanonicalTailExponential.regular w R C hw)
    (GaussianBarnesCanonicalPrefixDerivative.regular z R B hz) (GaussianBarnesCanonicalPrefixDerivative.regular w R C hw)
    (GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular z R B hz)
    (GaussianBarnesCanonicalTailExponentialDerivative.derivative_regular w R C hw) pre
    (GaussianBarnesCanonicalTailDerivativeFractionProperness.exponential_proper z w R B C hz hw eq)
    (prefix_proper z w R B C hz hw eq)
    (GaussianBarnesCanonicalTailDerivativeFractionProperness.derivative_proper z w R B C hz hw eq)

theorem fixed_reference_rate (w z h R C B : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalValueDerivative.input w h R C) (hz : Γ ⊢[PRAAx] source z R B)
    (eq : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w C) : Γ ⊢[PRAAx]
    independentRate quotientF nameF (quotientData w h R C) (data z R B) (numerator R h) (denominator R C) := by
  have hw : Γ ⊢[PRAAx] source w R C := hs.andE₂.andE₁
  have ev := GaussianBarnesCanonicalValue.regular w R C hw
  have hp := GaussianBarnesCanonicalValue.regular (ComplexLogarithmRemainder.add w h) R C hs.andE₂.andE₂.andE₁
  have q := GaussianNamedDifferenceQuotient.name_regular _ _ _ _ h C
    (.andI hp (.andI ev (.andI hw.andE₁ hs.andE₂.andE₂.andE₂.andE₁)))
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _
    (positive_product _ _ hw.andE₁ (initial_positive R)) (GaussianBarnesCanonicalValueDerivative.rate w h R C hs)
    (cross_refl _ _ q) (proper z w R B C hz hw eq)

theorem fixed_reference_precision (z R B p : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    independentRate quotientF nameF (quotientData (nativeBase z R p) oneCode (succ R) (nativeDenominator R B p))
      (data z (succ R) B) one (unit p) := by
  let w := nativeBase z R p
  let E := nativeDenominator R B p
  let S := succ R
  have info := GaussianBarnesCanonicalDerivativeStep.certified z R B p h
  have step := info.andE₂.andE₂.andE₁
  have source' : Γ ⊢[PRAAx] source z S B :=
    .andI h.andE₁ (bounded_mono h.andE₂ (mul_le_mul_right B (le_succ_self R)))
  have rt := fixed_reference_rate w z oneCode S E B step source' info.andE₁.eqSymm
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ step.andE₂.andE₁.andE₁ (initial_positive S)) (unit_positive p)
    (le_congr (.eqRefl _) (one_mul _).eqSymm info.andE₂.andE₂.andE₂) rt

theorem actual_Barnes_value_derivative_fraction_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let z := var 0
     let w := var 1
     let R := var 2
     let B := var 3
     let C := var 4
     (source z R B ⋏ (source w R C ⋏ (ofGaussian z B ≐ ofGaussian w C))) ⟶
       crossEquivalent nameF nameF (data z R B) (data w R C)) :=
  closeUniv 5 (.impI (proper _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_Barnes_derivative_fixed_reference_precision_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let p := var 3
     source z R B ⟶ independentRate quotientF nameF
       (quotientData (nativeBase z R p) oneCode (succ R) (nativeDenominator R B p)) (data z (succ R) B) one (unit p)) :=
  closeUniv 4 (.impI (fixed_reference_precision _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalValueDerivativeProperness
