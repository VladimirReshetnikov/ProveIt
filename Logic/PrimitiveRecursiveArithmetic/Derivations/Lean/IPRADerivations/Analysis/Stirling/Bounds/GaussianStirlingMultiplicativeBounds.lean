import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsLog
import IPRADerivations.Analysis.Stirling.Robbins.GaussianStirlingRobbins
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartTimeOrder
import IPRADerivations.Analysis.Gamma.EulerProducts.Convexity.GaussianGammaEulerRationalLogOrder

/-!
# Multiplicative bounds from the actual Stirling remainder

A positive lower logarithmic bound gives a rational factor above one.
The squared rectangle factor gives a rational upper bound strictly
below the usual relative-error cap.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBounds

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameBounds (U)
open GaussianNameEquivalence (cross_refl cross_symm cross_trans)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction logF data)
open GaussianRationalHorner (qadd qzero positive_product canonical)
open GaussianRationalMetric (qnegative)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingMultiplicative (quotientF quotientData reciprocalF reciprocalData multiplicative_formula)
open GaussianStirlingMultiplicativeAlgebra (remainderF remainderData remainder_regular)
open GaussianStirlingMultiplicativeBoundsLog (constant_order fractions_order logarithm_rectangles)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (firstTerm upperValue lowerValue upperMargin lowerMargin
  denominatorSquare square_positive small_numeral_positive upper_den_positive lower_den_positive)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "R" => GaussianStirlingMultiplicative.expRemainderF
local notation "RD" => GaussianStirlingMultiplicative.expRemainderData
local notation "quot" => GaussianStirlingGlobalBounds.finalUpper

def lowerFactor (m d : PTm n) : PTm n := fraction (d+m) d
def upperDen (a : PTm n) : PTm n := num 12*a
def upperBase (a b : PTm n) : PTm n := monus (two*upperDen a) b
def upperFactor (a b : PTm n) : PTm n :=
  fraction ((upperBase a b+b)*(upperBase a b+b)) (upperBase a b*upperBase a b)
def conventionalUpper (a b : PTm n) : PTm n := fraction (upperDen a) (monus (upperDen a) b)

private theorem frac_canonical (p q : PTm n) (hq : Γ ⊢[PRAAx] le one q) :
    Γ ⊢[PRAAx] canonical (fraction p q) :=
  GaussianRationalHorner.ofGaussian_canonical _ _ hq

private theorem axis_of_real (f : PR 2) (x : PTm n) (hr : Γ ⊢[PRAAx] realSamples f x) :
    Γ ⊢[PRAAx] GaussianRealNameExponentialInjectivity.axisSamples f x := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] realSamples f (Syn.shift x) := by
    simpa [Fm.shift,Syn.shift] using hr.shift
  exact (GaussianSignedNameExponentialOrder.real_sample_at f (Syn.shift x) (var 0) hs).andE₂

theorem remainder_real (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] realSamples remainderF (remainderData a b x) := by
  apply GaussianRealNameExponentialInjectivity.difference_real_samples
  · exact axis_of_real _ _ (GaussianStirlingNames.name_real a b hs)
  · exact axis_of_real _ _ (GaussianStirlingConstant.name_real x)

private theorem fraction_real (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples constantF (fraction a b) :=
  GaussianStirlingNames.constant_real _ (frac_canonical a b hb) (GaussianStirlingNames.fraction_axis a b hb)

private theorem log_real (a b : PTm n) : Γ ⊢[PRAAx] realSamples logF (data a b) := by
  refine .allI ?_
  let s := Syn.shift a
  let t := Syn.shift b
  have hc : Γ.map Fm.shift ⊢[PRAAx] canonical (ap2 logF (var 0) (data s t)) :=
    GaussianNameArithmetic.add_canonical _ _ _ _ _
  have h := GaussianRealNameExponentialInjectivity.axis_sample_at logF (data s t) (var 0)
    (GaussianNamedPositiveLogarithmScale.exact_rational_axis (Γ := Γ.map Fm.shift) s t)
  simpa [realSamples,Syn.shift,s,t] using Prf.andI hc h

private theorem exp_fraction (a b : PTm n) (hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent (E logF) constantF
      (GaussianGammaFiniteApproximantName.exponentialInputData logF (data a b)) (fraction a b) := by
  have first := GaussianExponentialRadiusIndependence.same_input_cross logF (U logF (data a b))
    (GaussianPositiveRationalLogarithm.radius a b) (data a b)
    (exponential_input _ _ (GaussianPositiveRationalLogarithm.name_regular _ _ hs))
    (GaussianPositiveRationalLogarithm.exponential_input _ _ hs)
  exact cross_trans _ _ _ _ _ _ first (GaussianPositiveRationalLogarithm.exponential_fraction a b hs)

private theorem negative_fraction (m d : PTm n) (hD : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] rationalLE (fstT (qnegative (fraction m d))) (fstT qzero) := by
  let v := ComplexLogarithmRemainder.scale m ComplexLogarithmRemainder.oneCode
  have rp := (GaussianRationalMetric.qnegative_represents _ _ _
    (GaussianRationalHorner.ofGaussian_represents v d hD)).andE₁
  have left : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qnegative (fraction m d))) (-(ZT.ofNat m)) d :=
    GaussianRationalHorner.scalar_congr (.eqRefl _) (by
      apply ZT.derive
      simp only [v,GaussianRootAlgebra.re_neg,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one,ZT.toZ_neg,ZT.toZ_ofNat]
      ring) (.eqRefl _) rp
  have zeroRep := GaussianRationalHorner.scalar_congr RationalGaussianRealPart.real_zero.eqSymm
    (.eqRefl _) (.eqRefl _) (RationalGaussianEmbedding.scalar_zero_represents (Γ := Γ) one)
  apply RationalArithmetic.order_of_representations _ _ _ _ d one left zeroRep hD (le_refl one)
  apply zle_of_toZ m
  ipra_simps
  ring

theorem weak_upper_log (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] realOrder constantF constantF (quot a b) (upperValue a b) := by
  let D := denominatorSquare a b
  let m := two*(b*b)*(b*b)
  let d := num 15*D*D
  let q := upperValue a b
  have hd := square_positive a b hs.andE₂
  have hM : Γ ⊢[PRAAx] le one d :=
    positive_product _ _ (positive_product _ _ (small_numeral_positive 14) hd) hd
  have h := point_add_order q q (qnegative (fraction m d)) qzero (point_order_refl q) (negative_fraction m d hM)
  exact constant_order _ _ (rationalLE_congr (.eqRefl _)
    (congrFst (GaussianReciprocalHorner.qadd_zero_right q (frac_canonical _ _ (upper_den_positive a hs.andE₁)))) h)

theorem weak_lower_log (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] realOrder constantF constantF (lowerValue a b) (GaussianStirlingRobbins.finalLower a b) := by
  let D := denominatorSquare a b
  let m := b*b*b*monus (num 24*a) (num 23*b)
  let d := num 3*D*(num 12*a+b)*(num 12*a+num 13*b)
  let q := lowerValue a b
  have hd := square_positive a b hs.andE₂
  have hA := upper_den_positive a hs.andE₁
  have hB := lower_den_positive a b hs.andE₁
  have hM : Γ ⊢[PRAAx] le one d :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ (small_numeral_positive 2) hd) hB)
      (le_trans hA (le_add_right _ _))
  have nonneg := rationalLE_congr RationalGaussianRealPart.real_zero.eqSymm (.eqRefl _)
    (GaussianRationalNonnegativeFractions.fraction_nonnegative m d hM).andE₁
  have h := point_add_order q q qzero (fraction m d) (point_order_refl q) nonneg
  exact constant_order _ _ (rationalLE_congr (congrFst (GaussianReciprocalHorner.qadd_zero_right q
    (frac_canonical _ _ hB))) (.eqRefl _) h)

theorem threshold_positive (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] le one (upperBase a b) ⋏ (upperBase a b+b ≐ two*upperDen a) := by
  let B := two*upperDen a
  have ha := hs.andE₁
  have far : Γ ⊢[PRAAx] le (one+b) B := by
    unfold B upperDen
    ipra_le sl hba+sl ha+22*𝔞 a
  have hb : Γ ⊢[PRAAx] le b B := le_trans (le_add_left _ _) far
  have eq := (eq_add_of_le hb).eqTrans (add_comm _ _)
  exact .andI (le_of_add_le_add_right (c := b) (le_congr (.eqRefl _) eq far)) eq.eqSymm

set_option maxHeartbeats 700000 in
theorem upper_log_barrier (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a) :
    Γ ⊢[PRAAx] realOrder constantF logF (upperValue a b)
      (data ((upperBase a b+b)*(upperBase a b+b)) (upperBase a b*upperBase a b)) := by
  let m := upperBase a b
  let P := m+b
  let c := fraction b P
  let x := data P m
  have h := threshold_positive a b hs hba
  have hp := le_trans h.andE₁ (le_add_right m b)
  have hu := upper_den_positive a hs.andE₁
  have rect := (logarithm_rectangles m b h.andE₁).andE₁
  have twoRect := GaussianGammaEulerRationalLogOrder.add_order constantF logF constantF logF c x c x rect rect
  have real := GaussianEulerPositiveTimePowerProduct.logarithm_product P m P m (.andI (.andI hp h.andE₁) (.andI hp h.andE₁))
  have read := GaussianStirlingOddCoefficients.fraction_add_same b b P hp
  have coeff := GaussianStirlingRationalTelescopers.fraction_same (b+b) P b (upperDen a)
    hp hu (by
      have e := natEq h.andE₂
      change 𝔞 P = 𝔞 (two*upperDen a) at e
      apply deriveNat
      ipra_simps
      linear_combination -𝔞 b*e)
  have bridge := GaussianNamedGammaHalfShift.constant_sum c c (upperValue a b) (read.eqTrans coeff)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ bridge)
    (cross_symm _ _ _ _ real) twoRect

theorem ratio_regular (a b x : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN quotientF (quotientData a b x) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (GaussianStirlingNames.gamma_regular a b hs)
    (GaussianStirlingLogDuplication.exponential_regular _ _
      (GaussianNameRingLaws.negative_fast _ _ (GaussianStirlingMultiplicativeAlgebra.normalization_regular a b x hs)))

set_option maxHeartbeats 800000 in
theorem relative_interval (a b x m d : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hba : Γ ⊢[PRAAx] le b a)
    (hd : Γ ⊢[PRAAx] le one d)
    (lower : Γ ⊢[PRAAx] realOrder constantF remainderF (fraction m d) (remainderData a b x))
    (upper : Γ ⊢[PRAAx] realOrder remainderF constantF (remainderData a b x) (quot a b)) :
    Γ ⊢[PRAAx] realOrder constantF quotientF (lowerFactor m d) (quotientData a b x) ⋏
      realOrder quotientF constantF (quotientData a b x) (upperFactor a b) := by
  let h := upperBase a b
  let p := h+b
  let y := remainderData a b x
  let xL := data (d+m) d
  let xH := data (p*p) (h*h)
  have lsrc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (d+m) d := .andI (le_trans hd (le_add_right _ _)) hd
  have hmin := (threshold_positive a b hs hba).andE₁
  have hpos := le_trans hmin (le_add_right h b)
  have hsrc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (p*p) (h*h) :=
    .andI (positive_product _ _ hpos hpos) (positive_product _ _ hmin hmin)
  have boundL := GaussianEulerPowerChartTimeOrder.order_trans logF constantF remainderF xL (fraction m d) y
    (logarithm_rectangles d m hd).andE₂ lower
  have boundHi := GaussianEulerPowerChartTimeOrder.order_trans constantF constantF logF (quot a b) (upperValue a b) xH
    (weak_upper_log a b hs) (upper_log_barrier a b hs hba)
  have boundH := GaussianEulerPowerChartTimeOrder.order_trans remainderF constantF logF y (quot a b) xH upper boundHi
  have hR := remainder_regular a b x hs
  have rReal := remainder_real a b x hs
  have expL := GaussianStirlingMultiplicativeBoundsOrder.exponential_order _ _ _ _
    (GaussianPositiveRationalLogarithm.name_regular _ _ lsrc) hR (log_real _ _) rReal boundL
  have expH := GaussianStirlingMultiplicativeBoundsOrder.exponential_order _ _ _ _
    hR (GaussianPositiveRationalLogarithm.name_regular _ _ hsrc) rReal (log_real _ _) boundH
  have ratio := multiplicative_formula a b x hs
  exact .andI
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
      (cross_symm _ _ _ _ (exp_fraction _ _ lsrc)) ratio expL)
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
      (cross_symm _ _ _ _ ratio) (exp_fraction _ _ hsrc) expH)

end LeanProofs.IPRA.Analysis.GaussianStirlingMultiplicativeBounds
