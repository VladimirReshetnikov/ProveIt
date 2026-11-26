import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.GaussianEulerPositivePowerChartOrder
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Powers.GaussianEulerLowerPowerOrder

/-!
# Exponent order for the original rational time powers

The harmonic logarithm observations have the correct sign at every
clock. Compare the original exponent coefficients using one common
product clock, then transport the exponential order to the original
time-power programs at their independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerChartExponentOrder

open_ipra
open GaussianEulerPositivePowerChart (argument)
open GaussianEulerPositivePowerChartOrder (inputF inputData input_cross coefficient_bound input_real_samples)
open GaussianEulerIntegrandName (powerF powerData powerExponentF powerExponentData powerRadius)
open GaussianHarmonicLogarithmName (sample)
open GaussianNamedPositiveExponentialOrder (sampleOrder realOrder)
open GaussianNameEquivalence (cross_symm)
open GaussianPositiveRationalLogarithm (fraction)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (e f u v Q a b : PTm n) : Fm PTm n :=
  (le one f ⋏ le e (Q*f)) ⋏ ((le one v ⋏ le u (Q*v)) ⋏
    (le (e*v) (u*f) ⋏ GaussianPositiveRationalLogarithm.source a b))

ipra_subst source

private theorem scalar_represents (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (fraction a b)) (ZT.ofNat a) b := by
  apply GaussianRationalHorner.scalar_congr (.eqRefl _) ?_ (.eqRefl _)
    (GaussianRationalHorner.ofGaussian_represents (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b hb).andE₁
  apply ZT.derive
  simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_ofNat]
  ring

theorem coefficient_order (e f u v : PTm n)
    (hf : Γ ⊢[PRAAx] le one f) (hv : Γ ⊢[PRAAx] le one v)
    (h : Γ ⊢[PRAAx] le (e*v) (u*f)) : Γ ⊢[PRAAx]
    rationalLE (fstT (fraction e f)) (fstT (fraction u v)) :=
  GaussianRationalMetric.comparison_of_cleared _ _ e u f v hf hv (scalar_represents e f hf) (scalar_represents u v hv)
    (le_congr (mul_comm e v) (.eqRefl _) h)

private theorem product_scalar_at (p e f Q a b : PTm n) : Γ ⊢[PRAAx]
    fstT (ap2 inputF p (inputData e f Q a b)) ≐
      RationalArithmetic.multiply (fstT (sample (GaussianBoundedConstantProductName.clock p Q) a b))
        (fstT (fraction e f)) := by
  let l := sample (GaussianBoundedConstantProductName.clock p Q) a b
  have axis := (GaussianHarmonicLogarithmName.sample_real (Γ := Γ) (GaussianBoundedConstantProductName.clock p Q) a b).andE₂
  exact (congrFst (GaussianBoundedConstantProductName.sample_at GaussianHarmonicLogarithmName.nameF p Q
    (fraction e f) (GaussianHarmonicLogarithmName.data a b))).eqTrans
      ((GaussianPositiveExponentialProduct.real_product (fraction e f) l axis).eqTrans (RationalAlgebra.multiply_commutative _ _))

theorem increasing_samples (e f u v Q a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f u v Q a b) (ht : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] sampleOrder inputF inputF (inputData e f Q a b) (inputData u v Q a b) := by
  refine .allI ?_
  let s (x : PTm n) : PTm (n+1) := Syn.shift x
  let p : PTm (n+1) := var 0
  have h : Γ.map Fm.shift ⊢[PRAAx] source (s e) (s f) (s u) (s v) (s Q) (s a) (s b) := by
    simpa only [Fm.shift,Syn.shift,subst_source,s] using hs.shift
  have order : Γ.map Fm.shift ⊢[PRAAx] le (s b) (s a) := by simpa [Fm.shift,Syn.shift,s] using ht.shift
  let t := GaussianBoundedConstantProductName.clock p (s Q)
  have raw := RationalArithmetic.multiply_monotone (fstT (sample t (s a) (s b))) (fstT (fraction (s e) (s f))) (fstT (fraction (s u) (s v)))
    (GaussianEulerUpperPowerCoefficients.harmonic_sample_nonnegative t _ _ order).andE₂
    (coefficient_order (s e) (s f) (s u) (s v) h.andE₁.andE₁ h.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁)
  simpa only [sampleOrder,Syn.shift,GaussianEulerPositivePowerChartOrder.subst_inputData,s,p] using
    rationalLE_congr (product_scalar_at p (s e) (s f) (s Q) (s a) (s b)).eqSymm
      (product_scalar_at p (s u) (s v) (s Q) (s a) (s b)).eqSymm raw

theorem decreasing_samples (e f u v Q a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f u v Q a b) (ht : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] sampleOrder inputF inputF (inputData u v Q a b) (inputData e f Q a b) := by
  refine .allI ?_
  let s (x : PTm n) : PTm (n+1) := Syn.shift x
  let p : PTm (n+1) := var 0
  have h : Γ.map Fm.shift ⊢[PRAAx] source (s e) (s f) (s u) (s v) (s Q) (s a) (s b) := by
    simpa only [Fm.shift,Syn.shift,subst_source,s] using hs.shift
  have order : Γ.map Fm.shift ⊢[PRAAx] le (s a) (s b) := by simpa [Fm.shift,Syn.shift,s] using ht.shift
  let t := GaussianBoundedConstantProductName.clock p (s Q)
  have raw := RationalArithmetic.multiply_antitone (fstT (sample t (s a) (s b))) (fstT (fraction (s e) (s f))) (fstT (fraction (s u) (s v)))
    (GaussianEulerLowerPowerCoefficients.harmonic_sample_nonpositive t _ _ order)
    (coefficient_order (s e) (s f) (s u) (s v) h.andE₁.andE₁ h.andE₂.andE₁.andE₁ h.andE₂.andE₂.andE₁)
  simpa only [sampleOrder,Syn.shift,GaussianEulerPositivePowerChartOrder.subst_inputData,s,p] using
    rationalLE_congr (product_scalar_at p (s u) (s v) (s Q) (s a) (s b)).eqSymm
      (product_scalar_at p (s e) (s f) (s Q) (s a) (s b)).eqSymm raw

private theorem transport_power_order (e f u v Q a b R : PTm n)
    (ht : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b)
    (he : Γ ⊢[PRAAx] le one f ⋏ le e (Q*f))
    (hu : Γ ⊢[PRAAx] le one v ⋏ le u (Q*v))
    (hleft : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input inputF R (inputData e f Q a b))
    (hright : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input inputF R (inputData u v Q a b))
    (ho : Γ ⊢[PRAAx] sampleOrder inputF inputF (inputData e f Q a b) (inputData u v Q a b)) :
    Γ ⊢[PRAAx] realOrder powerF powerF (powerData (argument e f) f a b) (powerData (argument u v) v a b) := by
  let x := inputData e f Q a b
  let y := inputData u v Q a b
  let z := argument e f
  let w := argument u v
  have order := GaussianSignedNameExponentialOrder.original_signed_name_order inputF inputF R x y hleft hright
    (input_real_samples e f Q a b he.andE₁) (input_real_samples u v Q a b hu.andE₁) ho
  have left := GaussianExponentialRadiusIndependence.independent_radii_proper inputF powerExponentF R (powerRadius z f a b)
    x (powerExponentData z f a b) hleft (GaussianEulerIntegrandName.power_input z f a b (.andI he.andE₁ ht))
    (input_cross e f Q a b he.andE₁ he.andE₂ ht)
  have right := GaussianExponentialRadiusIndependence.independent_radii_proper inputF powerExponentF R (powerRadius w v a b)
    y (powerExponentData w v a b) hright (GaussianEulerIntegrandName.power_input w v a b (.andI hu.andE₁ ht))
    (input_cross u v Q a b hu.andE₁ hu.andE₂ ht)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ left) right order

def originalOrder (e f u v a b : PTm n) : Fm PTm n :=
  realOrder powerF powerF (powerData (argument e f) f a b) (powerData (argument u v) v a b)

theorem increasing_power (e f u v Q a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f u v Q a b) (ht : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] originalOrder e f u v a b := by
  let R := Q*GaussianHarmonicLogarithmName.radius one a
  have h := hs.andE₂.andE₂.andE₂
  have he := hs.andE₁
  have hu := hs.andE₂.andE₁
  have hleft := GaussianEulerUpperPowerOrder.product_input Q (fraction e f) a b (.andI h ht)
    (coefficient_bound e f Q he.andE₁ he.andE₂)
  have hright := GaussianEulerUpperPowerOrder.product_input Q (fraction u v) a b (.andI h ht)
    (coefficient_bound u v Q hu.andE₁ hu.andE₂)
  exact transport_power_order e f u v Q a b R h he hu hleft hright (increasing_samples _ _ _ _ _ _ _ hs ht)

theorem decreasing_power (e f u v Q a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f u v Q a b) (ht : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] originalOrder u v e f a b := by
  let R := Q*GaussianHarmonicLogarithmName.radius b one
  have h := hs.andE₂.andE₂.andE₂
  have he := hs.andE₁
  have hu := hs.andE₂.andE₁
  have hleft := GaussianEulerLowerPowerOrder.product_input Q (fraction u v) a b (.andI h ht)
    (coefficient_bound u v Q hu.andE₁ hu.andE₂)
  have hright := GaussianEulerLowerPowerOrder.product_input Q (fraction e f) a b (.andI h ht)
    (coefficient_bound e f Q he.andE₁ he.andE₂)
  exact transport_power_order u v e f Q a b R h hu he hleft hright (decreasing_samples _ _ _ _ _ _ _ hs ht)

theorem actual_original_time_power_exponent_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      ((le (var 6) (var 5) ⟶ originalOrder (var 0) (var 1) (var 2) (var 3) (var 5) (var 6)) ⋏
        (le (var 5) (var 6) ⟶ originalOrder (var 2) (var 3) (var 0) (var 1) (var 5) (var 6)))) :=
  closeUniv 7 (.impI (.andI (.impI (increasing_power _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (decreasing_power _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0))))

open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem scaled_observations (p q e f u v d h S a b : PTm n)
    (hh : Γ ⊢[PRAAx] le one h) (hS : Γ ⊢[PRAAx] le d (S*h))
    (ho : Γ ⊢[PRAAx] originalOrder e f u v a b) : Γ ⊢[PRAAx]
    RationalValueBounds.upper (fstT (ap2 GaussianEulerPositivePowerChart.nameF p
      (GaussianEulerPositivePowerChart.data e f d h S a b))) (fstT (ap2 GaussianEulerPositivePowerChart.nameF q
      (GaussianEulerPositivePowerChart.data u v d h S a b))) (unit p+unit q) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let j := GaussianEulerPositivePowerChart.clock p S
  let k := GaussianEulerPositivePowerChart.clock q S
  let U := unit j
  let V := unit k
  let x := powerData (argument e f) f a b
  let y := powerData (argument u v) v a b
  have old := GaussianNamedPositiveExponentialOrder.real_order_at powerF powerF x y j k ho
  have scaled := GaussianEulerPositivePowerChartOrder.scale_upper d h (ap2 powerF j x) (ap2 powerF k y)
    (U+V) (U*V) hh old
  have hU : Γ ⊢[PRAAx] le (S*P) U := GaussianFastValueCut.query_budget S p
  have hV : Γ ⊢[PRAAx] le (S*Q) V := GaussianFastValueCut.query_budget S q
  have paid : Γ ⊢[PRAAx] le (d*(U+V)*(P*Q)) ((P+Q)*(h*(U*V))) := by
    ipra_le 𝔞(h*V*Q)*sl hU+𝔞(h*U*P)*sl hV+𝔞(P*Q*(U+V))*sl hS
  have native := RationalValueBounds.upper_mono _ _ _ _ (P+Q) (P*Q)
    (positive_product _ _ hh (positive_product _ _ (unit_positive j) (unit_positive k))) scaled paid
  exact RationalValueBounds.upper_congr
    (congrFst (GaussianEulerPositivePowerChart.sample_at p e f d h S a b)).eqSymm
    (congrFst (GaussianEulerPositivePowerChart.sample_at q u v d h S a b)).eqSymm (.eqRefl _) (.eqRefl _) native

theorem scaled_order (e f u v d h S a b : PTm n)
    (hh : Γ ⊢[PRAAx] le one h) (hS : Γ ⊢[PRAAx] le d (S*h))
    (ho : Γ ⊢[PRAAx] originalOrder e f u v a b) : Γ ⊢[PRAAx]
    realOrder GaussianEulerPositivePowerChart.nameF GaussianEulerPositivePowerChart.nameF
      (GaussianEulerPositivePowerChart.data e f d h S a b) (GaussianEulerPositivePowerChart.data u v d h S a b) := by
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  have dh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh h) := by
    simpa [Fm.shift,Syn.shift,sh,one] using hh.shift.shift
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (sh d) (sh S*sh h) := by
    simpa [Fm.shift,Syn.shift,sh] using hS.shift.shift
  have do' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] originalOrder (sh e) (sh f) (sh u) (sh v) (sh a) (sh b) := by
    simpa only [originalOrder,Fm.shift,Syn.shift,sh,
      GaussianNamedPositiveExponentialOrder.subst_realOrder,GaussianEulerIntegrandName.subst_powerData,
      GaussianEulerPositivePowerChart.subst_argument] using ho.shift.shift
  refine .allI (.allI ?_)
  simpa only [realOrder,Syn.shift,GaussianEulerPositivePowerChart.subst_data,sh] using
    scaled_observations (var 1) (var 0) (sh e) (sh f) (sh u) (sh v) (sh d) (sh h) (sh S) (sh a) (sh b) dh ds do'

end LeanProofs.IPRA.Analysis.GaussianEulerPowerChartExponentOrder
