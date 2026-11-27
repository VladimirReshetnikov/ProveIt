import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary
import IPRADerivations.Analysis.Names.Order.GaussianNamedRealOrderLinear

/-!
# The uniform logarithmic Wendel estimate

The positive rectangle bounds the reciprocal logarithm by `r/a`.
Multiplication by `s/b` and sign reversal place the original relative
logarithm between `-r*s/(b*a)` and zero, including both endpoints.
-/

set_option autoImplicit false
set_option maxHeartbeats 1650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelUniformLog

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerRationalLogOrder (order_refl)
open GaussianGammaRationalFractionalChord (harmonicF)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular)
open GaussianGammaRationalLogGautschi (ratioExponentData)
open GaussianGammaRationalLogWendel (relativeExponentF relativeExponentData relative_exponent_regular log_ratio_sum)
open GaussianGammaRationalWendelBoundary (difference_cross harmonic_one fractional_zero zero_data_cross
  relative_zero_step relative_full_step lower_zero_step)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiplyModulus multiply_at)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast zeroF zero_fast zero_at add_zero_left)
open GaussianNamedDifference (name_regular)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderLinear (negative_constant negative_order fractional_order)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qzero qmul qmul_canonical positive_product)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qmul_congr qmul_zero_right)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order logarithm_rectangles)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "C" => constantF
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => harmonicF

def error (a b r s : PTm n) : PTm n := fraction (s*r) (b*a)
def negativeError (a b r s : PTm n) : PTm n := qsub qzero (error a b r s)

theorem product_zero_right (c z x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF C zeroF) zeroF (multiplyData C zeroF c z) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNameArithmetic.multiply_fast _ _ _ _ (constant_regular _) (zero_fast _)) (zero_fast _)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let X := Syn.shift x
  let Z := Syn.shift z
  let B := Syn.shift c
  let p : PTm (n+1) := var 0
  let k := GaussianFastValueCut.exponent (multiplyModulus C zeroF B Z) p
  have read : Δ ⊢[PRAAx] ap2 (multiplyF C zeroF) p (multiplyData C zeroF B Z) ≐ qmul (ap2 C k B) (ap2 zeroF k Z) :=
    (multiply_at C zeroF B Z p).eqTrans (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have eq : Δ ⊢[PRAAx] qmul (ap2 C k B) (ap2 zeroF k Z) ≐ qzero := (qmul_congr (.eqRefl (ap2 C k B)) (zero_at k Z)).eqTrans (qmul_zero_right _)
  simpa [Syn.shift,Δ,X,Z,B,p] using read.eqTrans (eq.eqTrans (zero_at p X).eqSymm)

theorem fractional_inverse (a j b s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hj : Γ ⊢[PRAAx] le one j) :
    Γ ⊢[PRAAx] crossEquivalent L (negativeF L) (fractionalData s b a j) (negativeData (fractionalData s b j a)) := by
  let c := fraction s b
  let x := hd a j
  let y := hd j a
  let z := hd a a
  let u := fractionalData s b a j
  let v := fractionalData s b j a
  have hc := constant_regular (Γ := Γ) c
  have hx := GaussianHarmonicLogarithmName.name_regular a j (.andI ha hj)
  have hy := GaussianHarmonicLogarithmName.name_regular j a (.andI hj ha)
  have hz := GaussianHarmonicLogarithmName.name_regular a a (.andI ha ha)
  have hu := fractional_regular s b a j (.andI ha hj)
  have hv := fractional_regular s b j a (.andI hj ha)
  have split := GaussianNameRingLaws.distributive C H H c x y hc hx hy
  have fold := GaussianGammaAdjacentCutoff.multiply_cross C C (addF H H) H c c (addData x y) z hc hc
    (add_fast _ _ _ _ hx hy) hz (cross_refl _ _ hc) (log_ratio_sum a j a ha hj ha)
  have right := GaussianGammaAdjacentCutoff.multiply_cross C C H zeroF c c z (negativeData v) hc hc hz
    (zero_fast _) (cross_refl _ _ hc) (harmonic_one a (negativeData v) ha)
  have cut := product_zero_right (Γ := Γ) c (negativeData v) (negativeData v)
  have total := cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ fold (cross_trans _ _ _ _ _ _ right cut))
  have diff := difference_cross (addF L L) zeroF L L (addData u v) (negativeData v) v v
    (add_fast _ _ _ _ hu hv) (zero_fast _) hv hv total (cross_refl _ _ hv)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (GaussianNamedStrictOrderDifference.sum_sub_right L L u v hu hv))
    (cross_trans _ _ _ _ _ _ diff (add_zero_left (negativeF L) (negativeData v) (negative_fast _ _ hv)))

theorem lower_log (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder C L (negativeError a b r s) (fractionalData s b a (a+r)) := by
  let j := a+r
  let f := GaussianPositiveRationalLogarithm.logF
  let x := hd j a
  let y := fraction r a
  let u := fractionalData s b j a
  let t := error a b r s
  have hj : Γ ⊢[PRAAx] le one j := le_trans ha (le_add_right _ _)
  have h := (logarithm_rectangles a r ha).andE₂
  have ord := GaussianNamedRealOrderTransport.transport H f C C x (GaussianPositiveRationalLogarithm.data j a)
    y y (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original j a (.andI hj ha)))
    (cross_refl _ _ (constant_regular _)) h
  have hx := GaussianHarmonicLogarithmName.name_regular j a (.andI hj ha)
  have scale := fractional_order H C s b x y hb hx (constant_regular _) ord
  have eq := cross_trans _ _ _ _ _ _
    (GaussianGammaWeierstrassApproximant.constant_product_cross (fraction s b) y)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (GaussianEulerDampedTimeRate.fraction_product s b r a hb ha))
  have pos := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (fractional_regular s b j a (.andI hj ha))) eq scale
  have neg := negative_order L C u t (fractional_regular s b j a (.andI hj ha)) (constant_regular _) pos
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (negative_constant t)) (cross_symm _ _ _ _ (fractional_inverse a j b s ha hj)) neg

def logEndpoint (a b r s : PTm n) : Fm PTm n :=
  crossEquivalent L zeroF (fractionalData s b a (a+r)) (ratioExponentData a b r) ⋏
  crossEquivalent relativeExponentF zeroF (relativeExponentData a b r s) (ratioExponentData a b r)

def logWeak (a b r s : PTm n) : Fm PTm n :=
  realOrder L relativeExponentF (fractionalData s b a (a+r)) (relativeExponentData a b r s) ⋏
  realOrder relativeExponentF zeroF (relativeExponentData a b r s) (ratioExponentData a b r)

ipra_subst logEndpoint [relativeExponentData, ratioExponentData, fractionalData]

theorem log_endpoint_congr (a b r s r' s' : PTm n) (er : Γ ⊢[PRAAx] r ≐ r') (es : Γ ⊢[PRAAx] s ≐ s')
    (h : Γ ⊢[PRAAx] logEndpoint a b r s) : Γ ⊢[PRAAx] logEndpoint a b r' s' := by
  simpa using Prf.eqSubst (logEndpoint (var 0) (var 1) (var 2) (var 3) : Fm PTm 4) ![a,b,r,s] ![a,b,r',s']
    (fun i => by fin_cases i; exact .eqRefl a; exact .eqRefl b; exact er; exact es) (by simpa using h)

theorem log_weak_of_endpoint (a b r s : PTm n) (h : Γ ⊢[PRAAx] logEndpoint a b r s) :
    Γ ⊢[PRAAx] logWeak a b r s := by
  let z := ratioExponentData a b r
  have zOrd := order_refl zeroF z (zero_fast (Γ := Γ) z)
  exact .andI (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ h.andE₁ (cross_symm _ _ _ _ h.andE₂) zOrd)
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ h.andE₂ (cross_refl _ _ (zero_fast z)) zOrd)

theorem log_weak (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (e : Γ ⊢[PRAAx] b ≐ r+s) : Γ ⊢[PRAAx] logWeak a b r s := by
  refine .orE (zero_or_succ r) ?_ ?_
  · have er : (r ≐ zero) :: Γ ⊢[PRAAx] r ≐ zero := Prf.hyp0
    have es := e.wk.eqTrans ((congrAdd er (.eqRefl s)).eqTrans (zero_add s))
    have h : (r ≐ zero) :: Γ ⊢[PRAAx] logEndpoint a b zero b := Prf.andI (lower_zero_step a b ha.wk hb.wk) (relative_zero_step a b ha.wk hb.wk)
    exact log_weak_of_endpoint a b r s (log_endpoint_congr a b zero b r s er.eqSymm es h)
  · have er : (r ≐ succ (pred r)) :: Γ ⊢[PRAAx] r ≐ succ (pred r) := Prf.hyp0
    have hr := Order.zero_lt_of_eq_succ er
    refine .orE (zero_or_succ s) ?_ ?_
    · have es : (s ≐ zero) :: (r ≐ succ (pred r)) :: Γ ⊢[PRAAx] s ≐ zero := Prf.hyp0
      have er' := e.wk.wk.eqTrans ((congrAdd (.eqRefl r) es).eqTrans (add_zero r))
      have h : (s ≐ zero) :: (r ≐ succ (pred r)) :: Γ ⊢[PRAAx] logEndpoint a b b zero :=
        .andI (fractional_zero b a (a+b) (ratioExponentData a b b) hb.wk.wk
          (.andI ha.wk.wk (le_trans ha.wk.wk (le_add_right _ _))))
          (relative_full_step a b ha.wk.wk hb.wk.wk)
      exact log_weak_of_endpoint a b r s (log_endpoint_congr a b b zero r s er' es.eqSymm h)
    · have es : (s ≐ succ (pred s)) :: (r ≐ succ (pred r)) :: Γ ⊢[PRAAx] s ≐ succ (pred s) := Prf.hyp0
      have hs := Order.zero_lt_of_eq_succ es
      exact .andI
        (GaussianGammaRationalLogWendel.lower a b r s ha.wk.wk hb.wk.wk hr.wk hs e.wk.wk).andE₁
        (GaussianGammaRationalLogWendel.upper a b r s ha.wk.wk hb.wk.wk hr.wk hs e.wk.wk).andE₁

def logEstimate (a b r s : PTm n) : Fm PTm n :=
  realOrder C relativeExponentF (negativeError a b r s) (relativeExponentData a b r s) ⋏
  realOrder relativeExponentF zeroF (relativeExponentData a b r s) (ratioExponentData a b r)

theorem log_estimate (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (e : Γ ⊢[PRAAx] b ≐ r+s) : Γ ⊢[PRAAx] logEstimate a b r s := by
  have ord := log_weak a b r s ha hb e
  exact .andI (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ (lower_log a b r s ha hb) ord.andE₁) ord.andE₂

theorem quarter_error (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (e : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] realOrder C C (error a b r s) (fraction b (num 4*a)) := by
  have h := GaussianGammaEulerMidpointHeadGap.small_le_large (Γ := Γ) r s
  have he : Γ ⊢[PRAAx] le (num 4*(r*s)) (b*b) := le_congr (by unfold GaussianGammaEulerMidpointHeadGap.small; ipra_ring)
    (congrMul e.eqSymm e.eqSymm) h
  have h' : Γ ⊢[PRAAx] le ((num 4*a)*(s*r)) (b*(b*a)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right a he)
  exact constant_order _ _ (fractions_order _ _ _ _ (positive_product _ _ hb ha)
    (positive_product _ _ (zero_lt_succ (num 3)) ha) h')

theorem actual_positive_rational_Wendel_uniform_log_estimate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 0) ⋏ (le one (var 1) ⋏ var 1 ≐ var 2+var 3)) ⟶
      logEstimate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (log_estimate _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelUniformLog
