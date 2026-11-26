import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorGridComparison
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget
import IPRADerivations.Analysis.Names.Rates.GaussianNativeDerivativeQuotientRate
import IPRADerivations.Core.CommonLemmas

/-!
# Small-step convergence of the literal finite Barnes forward differences

The requested step radius is independent of the finite cutoff and the
separation witness. A later literal observation clock pays the grid
normalization and sampled scalar. The fixed-cutoff derivative name may
be observed at any independent clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (bounded bounded_mono normSq)
open GaussianBarnesCanonicalFiniteCentralExponential (finiteNameF finiteData)
open GaussianBarnesCanonicalFiniteTaylorGridComparison (value)
open GaussianBarnesCanonicalFiniteTaylorGridLeading (observationCost prefactorClock rational_readback scaled_leading)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid polynomialGrid scaledPolynomial observationCap)
open GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget
  (analyticCoefficient amplification rowNumerator rowDenominator)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (readbackGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1 normSq_le_norm1_square norm1_square_le_two_normSq)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianPolynomialForwardDifferenceGridError (rowBound row_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul qzero)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def stepCost (z R B M : PTm n) : PTm n :=
  previous M*stepDivisor R+num 4*analyticCoefficient z (R+one) B M

def stepClock (p z R B M : PTm n) : PTm n := exponent (stepCost z R B M) p

def coefficientClock (p z R B M : PTm n) : PTm n :=
  exponent (num 4*readbackGain z (R+one) B (previous M)) p

def polynomialClock (p z R B M : PTm n) : PTm n :=
  prefactorClock (coefficientClock p z R B M) z R B M+
    exponent (num 4*(amplification B M*GaussianBarnesCanonicalFiniteTaylorGridBudget.clockGain z (R+one) B)) p

def gridCost (q z h R B H r M : PTm n) : PTm n :=
  two+observationCap q z h R B H r M (previous M)

def observationClock (p z h R B r M : PTm n) : PTm n :=
  let q := polynomialClock p z R B M
  let H := norm1 h
  exponent (num 4*(amplification B M*gridCost q z h R B H r M+
    (one+observationCost q z R B H r M))) p

private theorem row_weaken (V W L A B C D : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D)
    (hfit : Γ ⊢[PRAAx] le (A*D) (C*B)) (hr : Γ ⊢[PRAAx] rowBound V W L A B) :
    Γ ⊢[PRAAx] rowBound V W L C D := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh L) :: Γ.map Fm.shift
  have hb' : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hb.shift.wk
  have hd' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hd.shift.wk
  have hf' : Δ ⊢[PRAAx] le (sh A*sh D) (sh C*sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hfit.shift.wk
  have hr' : Δ ⊢[PRAAx] rowBound (sh V) (sh W) (sh L) (sh A) (sh B) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hr.shift.wk
  exact distance_radius_mono _ _ _ _ _ _ hb' hd' hf' (row_at _ _ _ _ _ (var 0) hr' Prf.hyp0)

private theorem normalized_rows (t q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le ((previous M*stepDivisor R)*H) B) :
    Γ ⊢[PRAAx] rowBound (literalGrid t z h R B r (previous M)) (polynomialGrid t q z h R B H r M (previous M))
      (succ (previous M)) (rowNumerator q t z (R+one) B H M (gridCost q z h R B H r M))
      (rowDenominator q t B M) := by
  let U := unit t
  let e := previous M
  let S := R+one
  let A := GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator q z S B (e*H) M
  let D := GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q S B M
  let A' := GaussianBarnesCanonicalFiniteTaylorGridBudget.numerator q z S B H M
  let D' := GaussianBarnesCanonicalFiniteTaylorGridBudget.denominator q B M
  let C := observationCap q z h R B H r M e
  have cmp : Γ ⊢[PRAAx] le (A*D') (A'*D) :=
    GaussianBarnesCanonicalFiniteTaylorGridBudget.radius_comparison q z S B H M
  have hf : Γ ⊢[PRAAx] le ((A*U*U+D*(U+(one+C)*U))*(D'*U))
      ((A'*U+D'*(two+C))*(D*U*U)) := by
    ipra_le 𝔞(U)*𝔞(U)*𝔞(U)*sl cmp
  exact row_weaken _ _ _ _ _ _ _
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.denominator_positive t t q R B M hz.andE₁)
    (GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.row_denominator_positive q t B M hz.andE₁)
    hf (GaussianBarnesCanonicalFiniteTaylorGridObservations.row_bound t t q z h R B H r M e hz hh hs)

private theorem native_lower (h B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ofGaussian h B) (norm1 h) (two*B) := by
  apply lower_from_representation _ h B _ _ hb (positive_product _ _ (le_succ_self one) hb)
    (ofGaussian_represents h B hb)
  have hsq := norm1_square_le_two_normSq (Γ := Γ) h
  ipra_le 𝔞(B)*𝔞(B)*(sl hsq+2*𝔞(normSq h))

private theorem budget_sum (U V B Q T W a c d f g : PTm n)
    (ha : Γ ⊢[PRAAx] le (num 4*U*a) B) (hc : Γ ⊢[PRAAx] le (num 4*U*c) Q)
    (ht : Γ ⊢[PRAAx] le (num 4*U*(d+(one+f))) T) (hg : Γ ⊢[PRAAx] le (num 4*U*g) W) :
    let A := a*Q*T+c*B*T+d*B*Q
    let J := g*V*T+W*(V+T)+f*W*V
    let X := B*Q*T
    let Y := W*V*T
    Γ ⊢[PRAAx] le ((A*Y+J*X)*(U*V)) ((U+V)*(X*Y)) := by
  dsimp only
  apply Common.mul_cancel_le (show Γ ⊢[PRAAx] le one (num 4) from zero_lt_succ _)
  ipra_le (𝔞(V)*𝔞(Q)*𝔞(T)*𝔞(W*V*T))*sl ha+
    (𝔞(V)*𝔞(B)*𝔞(T)*𝔞(W*V*T))*sl hc+
    (𝔞(V)*𝔞(B)*𝔞(Q)*𝔞(W*V*T))*sl ht+
    (𝔞(V)*𝔞(V)*𝔞(T)*𝔞(B*Q*T))*sl hg

theorem rate (p z h R B r M t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hh : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p z R B M)) B)
    (ht : Γ ⊢[PRAAx] le (observationClock p z h R B r M) t) :
    Γ ⊢[PRAAx] distanceBounded (value t z h R B r M) (ap2 F u (fd z (R+one) B r M (previous M)))
      (unit p+unit u) (unit p*unit u) := by
  let S := R+one
  let e := previous M
  let H := norm1 h
  let k := coefficientClock p z R B M
  let q := polynomialClock p z R B M
  let K := gridCost q z h R B H r M
  let C := observationCost q z R B H r M
  let P := scaledPolynomial t q z R B H r M e
  let V := literalGrid t z h R B r e
  let w := ofGaussian h B
  let x := value t z h R B r M
  let y := qmul (ap2 finiteNameF t (finiteData z S B r))
    (GaussianBarnesCanonicalFiniteTaylorGridLeading.coefficient q z R B H r M)
  let v := ap2 F u (fd z S B r M e)
  let A := GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.numerator q t z S B H M K
  let D := GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.denominator q t B
  let J := GaussianBarnesCanonicalFiniteTaylorGridLeading.observationNumerator u t k q z R B H r M
  let E := rateDenominator (unit k) u t
  have hb := hz.andE₁
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have enlarged : Γ ⊢[PRAAx] source z S B :=
    .andI hb (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by dsimp only [S]; ipra_ring)))
  have stepPayment : Γ ⊢[PRAAx] le (stepCost z R B M*unit p) (unit (stepClock p z R B M)) :=
    query_budget _ _
  have admission : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B := by
    have hcost : Γ ⊢[PRAAx] le (e*stepDivisor R) (stepCost z R B M*unit p) :=
      le_trans (le_add_right _ _) (le_congr (one_mul _) (mul_comm _ _)
        (mul_le_mul_right (stepCost z R B M) (unit_positive p)))
    exact le_trans (le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right H (le_trans hcost stepPayment))) hh
  have payAnalytic : Γ ⊢[PRAAx] le (num 4*unit p*(analyticCoefficient z S B M*H)) B := by
    have lower : Γ ⊢[PRAAx] le (num 4*analyticCoefficient z S B M) (stepCost z R B M) :=
      le_add_left _ _
    have buy := mul_le_mul_right H (le_trans (le_mul_mono lower (le_refl (unit p))) stepPayment)
    exact le_trans (le_congr (by ipra_ring) (mul_comm _ _) buy) hh
  have prefactorReady : Γ ⊢[PRAAx] le (prefactorClock k z R B M) q := le_add_right _ _
  have payTaylor : Γ ⊢[PRAAx] le (num 4*unit p*
      (amplification B M*GaussianBarnesCanonicalFiniteTaylorGridBudget.clockGain z S B)) (unit q) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (query_budget
      (num 4*(amplification B M*GaussianBarnesCanonicalFiniteTaylorGridBudget.clockGain z S B)) p))
      (unit_monotone (le_add_left _ _))
  have payClock : Γ ⊢[PRAAx] le (num 4*unit p*(amplification B M*K+(one+C))) (unit t) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _)
      (query_budget (num 4*(amplification B M*K+(one+C))) p)) (unit_monotone ht)
  have payCoefficient : Γ ⊢[PRAAx] le (num 4*unit p*readbackGain z S B e) (unit k) :=
    le_congr (by ipra_ring) (.eqRefl _) (query_budget (num 4*readbackGain z S B e) p)
  have raw := GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.coefficient_error
    q t z S B H M K V P qzero w hb hH
    (GaussianBarnesCanonicalFiniteTaylorGridObservations.scaled_polynomial_length t q z R B H r M e)
    (native_lower h B hb) (normalized_rows t q z h R B H r M hz (normSq_le_norm1_square h) admission)
  have fromGrid : Γ ⊢[PRAAx] distanceBounded x y A D :=
    distance_congr (.eqRefl _) (scaled_leading (ap2 finiteNameF t (finiteData z S B r)) q z R B H r M)
      (.eqRefl _) (.eqRefl _) raw
  have hd : Γ ⊢[PRAAx] le one D := GaussianBarnesCanonicalFiniteTaylorNormalizedGridBudget.denominator_positive q t B hb
  have he : Γ ⊢[PRAAx] le one E := GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive k)
  have whole := positive_product _ _ hd he
  have fromCoefficient : Γ ⊢[PRAAx] distanceBounded y v J E :=
    distance_symmetric _ _ _ _ he (rational_readback u t k q z R B H r M enlarged prefactorReady)
  have first : Γ ⊢[PRAAx] distanceBounded x y (A*E) (D*E) :=
    distance_radius_mono _ _ _ _ _ _ hd whole (le_of_eq_add (d := zero) (by ipra_ring)) fromGrid
  have next : Γ ⊢[PRAAx] distanceBounded y v (J*D) (D*E) :=
    distance_radius_mono _ _ _ _ _ _ he whole (le_of_eq_add (d := zero) (by ipra_ring)) fromCoefficient
  exact distance_radius_mono _ _ _ _ _ _ whole (positive_product _ _ (unit_positive p) (unit_positive u))
    (budget_sum (unit p) (unit u) B (unit q) (unit t) (unit k)
      (analyticCoefficient z S B M*H) (amplification B M*GaussianBarnesCanonicalFiniteTaylorGridBudget.clockGain z S B)
      (amplification B M*K) C (readbackGain z S B e) payAnalytic payTaylor payClock payCoefficient)
    (distance_triangle_same _ _ _ _ _ _ whole first next)

theorem actual_Barnes_finite_normalized_grid_small_step_limit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     let t := var 7
     let u := var 8
     source z R B ⟶ le one (normSq h) ⟶ le (norm1 h*unit (stepClock p z R B M)) B ⟶
       le (observationClock p z h R B r M) t ⟶
       distanceBounded (value t z h R B r M) (ap2 F u (fd z (R+one) B r M (previous M)))
         (unit p+unit u) (unit p*unit u)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (rate _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridLimit
