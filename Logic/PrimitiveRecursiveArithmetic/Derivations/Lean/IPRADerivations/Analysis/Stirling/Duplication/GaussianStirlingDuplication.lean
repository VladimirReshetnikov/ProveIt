import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationAlgebra
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationConstant
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationLogs
import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingRecurrence

/-!
# The exact named Stirling duplication identity

The original logarithmic duplication and the three positive rational
logarithms give independent-clock observation estimates. Their exact
rational cancellation identifies the original difference of the three
Stirling names with the original constant and the small logarithmic term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDuplication

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGaussMultiplicationPowerRate (multiplier limitLogData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast sum_distance)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (crossEquivalent cross_diagonal_at)
open GaussianNameRingLaws (add_sample_error multiply_sample_error product_right_error negativeF negativeData
  negative_sample_error through_identity)
open GaussianNamedDifference (difference_distance)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd qmul)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalSyntheticDivision (qmul_congr qzero_add qadd_sub_cancel)
open GaussianStirlingDifferenceAlgebra (rawA)
open GaussianStirlingDuplicationAlgebra (rawHalfGamma rawResidual rawConstant duplication_value)
open GaussianStirlingDuplicationLogs (halfRatioData logTwoData half_log double_log rational_inverse)
open GaussianStirlingLogDuplication (powerExponentF powerExponentData power_regular)
open GaussianStirlingNativeDuplication (halfNumerator halfDenominator half_source double_source)
open GaussianStirlingNames (source arg nameF nameData name_regular logGammaF logGammaData log_gamma_regular
  logXF logXData log_x_regular point)
open GaussianStirlingRecurrence (scaleBudget aBudget a_error)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "three" => GaussianNameRingLaws.three
local notation "CF" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData
local notation "LL" => GaussianStirlingLogDuplication.leftF
local notation "LD" => GaussianStirlingLogDuplication.leftData
local notation "RR" => GaussianStirlingLogDuplication.rightF
local notation "RD" => GaussianStirlingLogDuplication.rightData

def residualProductF : PR 2 := multiplyF constantF logF
def residualProductData (a b : PTm n) : PTm n :=
  multiplyData constantF logF (point a b) (halfRatioData a b)
abbrev residualF : PR 2 := GaussianNamedDifference.nameF constantF residualProductF
def residualData (a b : PTm n) : PTm n := GaussianNamedDifference.data (fraction one two) (residualProductData a b)
abbrev leftSumF : PR 2 := addF nameF nameF
def leftSumData (a b : PTm n) : PTm n :=
  addData (nameData a b) (nameData (halfNumerator a b) (halfDenominator b))
abbrev leftF : PR 2 := GaussianNamedDifference.nameF leftSumF nameF
def leftData (a b : PTm n) : PTm n := GaussianNamedDifference.data (leftSumData a b) (nameData (two*a) b)
abbrev rightF : PR 2 := addF CF residualF
def rightData (a b x : PTm n) : PTm n := addData (cd x) (residualData a b)

theorem half_ratio_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN logF (halfRatioData a b) :=
  GaussianPositiveRationalLogarithm.name_regular _ _ (.andI (half_source a b h).andE₁ (double_source a b h).andE₁)

theorem residual_regular (a b : PTm n) (h : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] pointCN residualF (residualData a b) :=
  GaussianNamedDifference.name_regular _ _ _ _ (constant_regular _)
    (multiply_fast constantF logF _ _ (constant_regular _) (half_ratio_regular a b h))

private theorem sum_near (f g : PR 2) (p x y u v A B : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hu : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) u A (unit p))
    (hv : Γ ⊢[PRAAx] distanceBounded (ap2 g p y) v B (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (addF f g) p (addData x y)) (qadd u v) (three+(A+B)) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (add_sample_error _ _ _ _ p hf hg)
    (sum_distance _ _ _ _ _ _ _ (unit_positive p) hu hv)

private theorem constant_near (p v : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 constantF p v) v zero (unit p) :=
  distance_congr (constant_at (Γ := Γ) p v).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (distance_refl_zero _ _ (unit_positive p))

private theorem multiply_near (f : PR 2) (p c x v A : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hv : Γ ⊢[PRAAx] distanceBounded (ap2 f p x) v A (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF constantF f) p (multiplyData constantF f c x)) (qmul c v)
      (scaleBudget f c x A) (unit p) := by
  have hc := constant_regular (Γ := Γ) c
  have first := multiply_sample_error constantF f c x p hc hf
  have exactAt := constant_at (Γ := Γ) p c
  have bounded := GaussianRationalReciprocal.bound_congr exactAt (.eqRefl _) (.eqRefl _) (sample_bound constantF c p hc)
  have last := product_right_error c _ v A (unit p) (U f x) (U constantF c) (unit_positive p) hv
    (sample_bound f x p hf) bounded
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qmul_congr exactAt (.eqRefl _)) (.eqRefl _) (.eqRefl _) first) last

private theorem nominal_sum (f g h : PR 2) (p x y z : PTm n) (hf : Γ ⊢[PRAAx] pointCN g y)
    (hg : Γ ⊢[PRAAx] pointCN h z) (he : Γ ⊢[PRAAx] crossEquivalent f (addF g h) x (addData y z)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (qadd (ap2 g p y) (ap2 h p z)) (two+three) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p) (cross_diagonal_at p he)
    (add_sample_error g h y z p hf hg)

def powerBudget (a b : PTm n) : PTm n :=
  scaleBudget logF (multiplier (arg a) b two) (limitLogData two) (two+three)

private theorem power_near (p a b : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 powerExponentF p (powerExponentData a b))
      (qmul (multiplier (arg a) b two) (qnegative (ap2 logF p (logTwoData : PTm n)))) (powerBudget a b) (unit p) := by
  let y : PTm n := logTwoData
  let u := ap2 logF p y
  have h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source one two := .andI (le_refl one) (le_succ_self one)
  have regular := GaussianPositiveRationalLogarithm.name_regular two one (.andI h.andE₂ h.andE₁)
  have n := negative_sample_error logF y p regular
  have eq := qzero_add (Γ := Γ) _ (GaussianRationalMetric.qnegative_canonical u)
  have d := cross_diagonal_at p (rational_inverse one two h)
  exact multiply_near logF p (multiplier (arg a) b two) (limitLogData two) (qnegative u) (two+three)
    (GaussianPositiveRationalLogarithm.name_regular one two h)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) d (distance_congr (.eqRefl _) eq (.eqRefl _) (.eqRefl _) n))

def halfGammaBudget (a b : PTm n) : PTm n :=
  (three+(two+(three+((three+(powerBudget a b+zero))+zero))))+zero

private theorem halfGamma_near (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 logGammaF p (logGammaData (halfNumerator a b) (halfDenominator b)))
      (rawHalfGamma a b (ap2 logGammaF p (logGammaData a b)) (ap2 logGammaF p (logGammaData one two))
        (ap2 logGammaF p (logGammaData (two*a) b)) (ap2 logF p (logTwoData : PTm n)))
      (halfGammaBudget a b) (unit p) := by
  let g := logGammaData a b
  let h : PTm n := logGammaData one two
  let j := logGammaData (two*a) b
  let k := logGammaData (halfNumerator a b) (halfDenominator b)
  let G := ap2 logGammaF p g
  let H := ap2 logGammaF p h
  let J := ap2 logGammaF p j
  let V := ap2 logF p (logTwoData : PTm n)
  let X := powerExponentData a b
  let Y := qmul (multiplier (arg a) b two) (qnegative V)
  let S := addF powerExponentF logGammaF
  let T := addData X h
  have bp := unit_positive (Γ := Γ) p
  have gh := log_gamma_regular a b hs
  have hh := log_gamma_regular one two (.andI (le_refl one) (le_succ_self one) : Γ ⊢[PRAAx] source one two)
  have jh := log_gamma_regular _ _ (double_source a b hs)
  have kh := log_gamma_regular _ _ (half_source a b hs)
  have first := distance_symmetric _ _ _ _ bp (add_sample_error logGammaF logGammaF g k p gh kh)
  have middle := cross_diagonal_at p
    (GaussianStirlingLogDuplication.logarithmic_duplication a b hs)
  have xh := power_regular (Γ := Γ) a b
  have partialSum := sum_near powerExponentF logGammaF p X h Y H (powerBudget a b) zero xh hh
    (power_near p a b) (distance_refl_zero _ _ bp)
  have last := sum_near S logGammaF p T j (qadd Y H) J (three+(powerBudget a b+zero)) zero
    (add_fast _ _ _ _ xh hh) jh partialSum (distance_refl_zero _ _ bp)
  have v := distance_triangle_same _ _ _ _ _ _ bp first (distance_triangle_same _ _ _ _ _ _ bp middle last)
  have w := difference_distance _ _ G G _ zero _ bp v (distance_refl_zero G _ bp)
  have eq := qadd_sub_cancel G (ap2 logGammaF p k)
    (GaussianSignedNameExponentialOrder.real_sample_at _ _ p
      (GaussianStirlingNames.log_gamma_real (Γ := Γ) (halfNumerator a b) (halfDenominator b))).andE₁
  exact distance_congr eq (.eqRefl _) (.eqRefl _) (.eqRefl _) w

def constantBudget : PTm n :=
  two+(three+(zero+scaleBudget logF (fraction one two) logTwoData zero))

private theorem stirling_constant_near (p x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 CF p (cd x))
      (rawConstant (ap2 logGammaF p (logGammaData one two)) (ap2 logF p (logTwoData : PTm n)))
      constantBudget (unit p) := by
  let h : PTm n := logGammaData one two
  let v : PTm n := logTwoData
  let c : PTm n := fraction one two
  let P := GaussianStirlingDuplicationConstant.halfLogTwoF
  let X : PTm n := GaussianStirlingDuplicationConstant.halfLogTwoData
  have bp := unit_positive (Γ := Γ) p
  have hh := log_gamma_regular one two (.andI (le_refl one) (le_succ_self one) : Γ ⊢[PRAAx] source one two)
  have vh := GaussianPositiveRationalLogarithm.name_regular
    two one (.andI (le_succ_self one) (le_refl one) : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source two one)
  have first := cross_diagonal_at p (GaussianStirlingDuplicationConstant.constant_half_gamma (Γ := Γ) x)
  have prod := multiply_near logF p c v (ap2 logF p v) zero vh (distance_refl_zero _ _ bp)
  have last := sum_near logGammaF P p h X (ap2 logGammaF p h) (qmul c (ap2 logF p v))
    zero (scaleBudget logF c v zero) hh (multiply_fast constantF logF c v (constant_regular c) vh)
    (distance_refl_zero _ _ bp) prod
  exact distance_triangle_same _ _ _ _ _ _ bp first last

def residualBudget (a b : PTm n) : PTm n :=
  num 6+(zero+scaleBudget logF (point a b) (halfRatioData a b) zero)

private theorem residual_near (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 residualF p (residualData a b)) (rawResidual a b (ap2 logF p (halfRatioData a b)))
      (residualBudget a b) (unit p) := by
  let c : PTm n := fraction one two
  let x := halfRatioData a b
  let y := point a b
  have bp := unit_positive (Γ := Γ) p
  have xh := half_ratio_regular a b hs
  have prod := multiply_near logF p y x (ap2 logF p x) zero xh (distance_refl_zero _ _ bp)
  have first := GaussianNamedDifference.sample_error constantF residualProductF c (residualProductData a b) p
    (constant_regular c) (multiply_fast constantF logF y x (constant_regular y) xh)
  exact distance_triangle_same _ _ _ _ _ _ bp first
    (difference_distance _ _ _ _ _ _ _ bp (constant_near p c) prod)

def duplicationBudget (a b : PTm n) : PTm n :=
  (num 6+((three+(aBudget a b zero zero+
    aBudget (halfNumerator a b) (halfDenominator b) (halfGammaBudget a b) (two+three)))+
    aBudget (two*a) b zero (two+three)))+(three+(constantBudget+residualBudget a b))

set_option maxHeartbeats 2200000 in
theorem duplication_error (p a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 leftF p (leftData a b)) (ap2 rightF p (rightData a b x))
      (duplicationBudget a b) (unit p) := by
  let A := halfNumerator a b
  let B := halfDenominator b
  let g := ap2 logGammaF p (logGammaData a b)
  let h := ap2 logGammaF p (logGammaData one two)
  let j := ap2 logGammaF p (logGammaData (two*a) b)
  let u := ap2 logXF p (logXData a b)
  let v := ap2 logF p (logTwoData : PTm n)
  let w := ap2 logF p (halfRatioData a b)
  have bp := unit_positive (Γ := Γ) p
  have lh := log_x_regular a b hs
  have vh := GaussianPositiveRationalLogarithm.name_regular two one
    (.andI (le_succ_self one) (le_refl one) : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source two one)
  have wh := half_ratio_regular a b hs
  have hh := half_source a b hs
  have dh := double_source a b hs
  have halfLog := nominal_sum logXF logXF logF p (logXData A B) (logXData a b) (halfRatioData a b) lh wh (half_log a b hs)
  have doubleLog := nominal_sum logXF logXF logF p (logXData (two*a) b) (logXData a b) logTwoData lh vh (double_log a b hs)
  have e0 := a_error p a b g u zero zero hs (distance_refl_zero _ _ bp) (distance_refl_zero _ _ bp)
  have eH := a_error p A B (rawHalfGamma a b g h j v) (qadd u w) (halfGammaBudget a b) (two+three) hh
    (halfGamma_near p a b hs) halfLog
  have eD := a_error p (two*a) b j (qadd u v) zero (two+three) dh (distance_refl_zero _ _ bp) doubleLog
  have reg0 := name_regular a b hs
  have regH := name_regular A B hh
  have regD := name_regular (two*a) b dh
  have eS := sum_near nameF nameF p (nameData a b) (nameData A B) (rawA a b g u)
    (rawA A B (rawHalfGamma a b g h j v) (qadd u w)) _ _ reg0 regH e0 eH
  have first := GaussianNamedDifference.sample_error leftSumF nameF (leftSumData a b) (nameData (two*a) b) p
    (add_fast _ _ _ _ reg0 regH) regD
  have left := distance_triangle_same _ _ _ _ _ _ bp first (difference_distance _ _ _ _ _ _ _ bp eS eD)
  have right := sum_near CF residualF p (cd x) (residualData a b) (rawConstant h v) (rawResidual a b w)
    constantBudget (residualBudget a b) (GaussianStirlingConstant.name_regular x)
    (residual_regular a b hs) (stirling_constant_near p x) (residual_near p a b hs)
  exact through_identity _ _ _ _ _ _ _ bp left right (duplication_value a b g h j u v w hs.andE₂)

private theorem subst_left {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (leftData a b) = leftData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [leftData,leftSumData,halfNumerator,halfDenominator,two]

private theorem subst_right {m : ℕ} (σ : Fin n → PTm m) (a b x : PTm n) :
    Syn.subst σ (rightData a b x) = rightData (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ x) := by
  simp [rightData,residualData,residualProductData,halfRatioData,halfNumerator,one,two]

private theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (duplicationBudget a b) = duplicationBudget (Syn.subst σ a) (Syn.subst σ b) := by
  simp [duplicationBudget,constantBudget,residualBudget,halfGammaBudget,powerBudget,aBudget,scaleBudget,
    halfNumerator,halfDenominator,halfRatioData,logTwoData,GaussianNameRingLaws.three,one,two]

set_option maxHeartbeats 2200000 in
theorem duplication (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent leftF rightF (leftData a b) (rightData a b x) := by
  have hs0 := name_regular a b hs
  have hsH := name_regular _ _ (half_source a b hs)
  have hsD := name_regular _ _ (double_source a b hs)
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (duplicationBudget a b)
    (GaussianNamedDifference.name_regular leftSumF nameF (leftSumData a b) (nameData (two*a) b)
      (add_fast _ _ _ _ hs0 hsH) hsD)
    (add_fast CF residualF (cd x) (residualData a b) (GaussianStirlingConstant.name_regular x) (residual_regular a b hs))
    (.allI ?_)
  have shifted : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift,Syn.shift,GaussianStirlingGammaLogarithm.subst_source] using hs.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,subst_left,subst_right,subst_budget] using
    duplication_error (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift x) shifted

set_option maxHeartbeats 2200000 in
theorem actual_positive_rational_Stirling_duplication_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ crossEquivalent leftF rightF (leftData (var 0) (var 1))
      (rightData (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (duplication (var 0) (var 1) (var 2) Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianStirlingDuplication
