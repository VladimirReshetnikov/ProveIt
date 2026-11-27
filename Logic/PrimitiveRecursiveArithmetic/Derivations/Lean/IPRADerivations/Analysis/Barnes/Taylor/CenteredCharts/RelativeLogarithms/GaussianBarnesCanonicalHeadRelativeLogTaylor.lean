/-
Second-order estimate for the original kept Barnes base-power logarithm.
The polynomial quadratic term and the Mercator square both have explicit
cubic errors on the certified zero-free chart.
-/
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.RelativeLogarithms.GaussianBarnesCanonicalHeadRelativeLogMargin
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalHeadPolynomialTaylor
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmQuadraticRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRationalSquareCancellation
import IPRADerivations.Analysis.Polynomials.Coefficients.Operations.GaussianPolynomialCoefficientDifferences

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeLogTaylor

open_ipra
open GaussianBarnesCanonicalBaseProductShift (powerProduct)
open GaussianBarnesCanonicalHeadRelativeLog (relative numerator denominator radius nameF data)
open GaussianBarnesCanonicalHeadRelativeLogMargin (gain relative_bound source_of_small)
open GaussianBarnesCanonicalHeadPolynomialDerivative (input powerSlope slopeCap linear step_bound)
open GaussianFiniteLogarithmPolynomial (coefficient)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedDifferenceRate (rate_parameters_congr)
open GaussianRationalHorner (qadd qmul ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Q" => GaussianBarnesCanonicalHeadPolynomialTaylor.quadratic
local notation "secondError" => GaussianBarnesCanonicalHeadPolynomialTaylor.errorGain
local notation "firstError" => GaussianBarnesCanonicalHeadPolynomialDerivative.errorGain
local notation "Merc" => GaussianLocalLogarithmQuadraticRate.quadratic
local notation "mercNum" => GaussianLocalLogarithmQuadraticRate.errorNumerator
local notation "mercDen" => GaussianLocalLogarithmQuadraticRate.errorDenominator

def inverse (z B N : PTm n) : PTm n := reciprocal (powerProduct z B N)
def relativeLinear (z h B N : PTm n) : PTm n := qmul (inverse z B N) (linear z h B N)

def quadratic (z h B N : PTm n) : PTm n :=
  qadd (qmul (inverse z B N) (Q z h B N))
    (qmul (coefficient one) (qmul (relativeLinear z h B N) (relativeLinear z h B N)))

def rationalGain (R N M : PTm n) : PTm n :=
  M*secondError R N + (M*firstError R N)*(gain R N M+M*slopeCap R N)

def errorGain (R N M : PTm n) : PTm n := gain R N M*gain R N M*gain R N M+rationalGain R N M

def source (z h R B H N M : PTm n) : Fm PTm n :=
  input z h R B H ⋏ (le H B ⋏ (le one M ⋏
    (GaussianNameReciprocal.lower (powerProduct z B N) M ⋏ le (num 4*(gain R N M*H)) B)))

@[simp] theorem subst_quadratic {m : ℕ} (σ : Fin n → PTm m) (z h B N : PTm n) :
    Syn.subst σ (quadratic z h B N) = quadratic (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [quadratic,relativeLinear,inverse,linear,powerSlope]

@[simp] theorem subst_errorGain {m : ℕ} (σ : Fin n → PTm m) (R N M : PTm n) :
    Syn.subst σ (errorGain R N M) = errorGain (Syn.subst σ R) (Syn.subst σ N) (Syn.subst σ M) := by
  simp [errorGain,rationalGain,GaussianBarnesCanonicalHeadPolynomialDerivative.errorGain,slopeCap]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h R B H N M : PTm n) :
    (source z h R B H N M).subst σ =
      source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ N) (Syn.subst σ M) := by
  simp [source]

private theorem scale_distance (t u v M A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] bounded t M one) (hd : Γ ⊢[PRAAx] distanceBounded u v A B) : Γ ⊢[PRAAx]
    distanceBounded (qmul t u) (qmul t v) (M*A) B :=
  bound_congr (GaussianRationalRoundedPower.multiplication_difference t u v).eqSymm (.eqRefl _) (one_mul B)
    (bounded_product _ _ _ _ _ _ (le_refl one) hB ht hd)

private theorem quadratic_coefficient_bound : Γ ⊢[PRAAx] bounded (coefficient (one : PTm n)) one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_succ_self one) (le_refl one)
    (Common.mul_le_mul (le_refl one) (le_succ_self one))
    (GaussianFiniteLogarithmTaylorRemainder.coefficient_bound one)

theorem rational_error (z h R B H N M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H N M) : Γ ⊢[PRAAx]
    distanceBounded (Merc (relative z h B N)) (quadratic z h B N) (rationalGain R N M*H*H*H) (B*B*B) := by
  let i := inverse z B N
  let g := gain R N M
  let j := M*firstError R N
  let l := M*slopeCap R N
  let f := M*secondError R N
  let w := relative z h B N
  let v := relativeLinear z h B N
  let u := qmul i (Q z h B N)
  let c : PTm n := coefficient one
  have hi := hs.andE₁
  have hB := hi.andE₁
  have hBB := positive_product _ _ hB hB
  have hBBB := positive_product _ _ hBB hB
  have m := hs.andE₂.andE₂.andE₁
  have lower := hs.andE₂.andE₂.andE₂.andE₁
  have inv : Γ ⊢[PRAAx] bounded i M one := GaussianNameReciprocal.inverse_bound _ _ m lower
  have hw : Γ ⊢[PRAAx] bounded w (g*H) B :=
    relative_bound z h R B H N M hi hs.andE₂.andE₁ m lower
  have hl : Γ ⊢[PRAAx] bounded (linear z h B N) (H*slopeCap R N) B :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ hB (le_refl one) (step_bound h B H hB hi.andE₂.andE₂.andE₂)
        (GaussianBarnesCanonicalHeadPolynomialDerivative.slope_bound z R B N hB hi.andE₂.andE₁))
  have hv : Γ ⊢[PRAAx] bounded v (l*H) B := bound_congr (.eqRefl _) (by dsimp only [l]; ipra_ring) (one_mul B)
    (bounded_product _ _ _ _ _ _ (le_refl one) hB inv hl)
  have first : Γ ⊢[PRAAx] distanceBounded w v (j*H*H) (B*B) :=
    bound_congr (.eqRefl _) (by dsimp only [j]; ipra_ring) (.eqRefl _)
      (scale_distance i _ _ M _ (B*B) hBB inv
        (GaussianBarnesCanonicalHeadPolynomialDerivative.quadratic_bound z h R B H N hi))
  have second : Γ ⊢[PRAAx] distanceBounded w u (f*H*H*H) (B*B*B) :=
    bound_congr (.eqRefl _) (by dsimp only [f]; ipra_ring) (.eqRefl _)
      (scale_distance i _ _ M _ (B*B*B) hBBB inv
        (GaussianBarnesCanonicalHeadPolynomialTaylor.cubic_bound z h R B H N hi))
  have sum := GaussianRationalPowerDifference.bounded_sum_same w v (g*H) (l*H) B hB hw hv
  have squared : Γ ⊢[PRAAx] distanceBounded (qmul w w) (qmul v v) (j*(g+l)*H*H*H) (B*B*B) :=
    bound_congr (GaussianRationalSquareCancellation.difference_factorization w v).eqSymm (by ipra_ring) (.eqRefl _)
      (bounded_product _ _ _ _ _ _ hBB hB first sum)
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul c (qmul w w)) (qmul c (qmul v v))
      (j*(g+l)*H*H*H) (B*B*B) :=
    bound_congr (.eqRefl _) (one_mul _) (.eqRefl _)
      (scale_distance c _ _ one _ _ hBBB quadratic_coefficient_bound squared)
  have exactDiff := GaussianPolynomialCoefficientDifferences.scalar_sum_difference (Γ := Γ)
    w u (qmul c (qmul w w)) (qmul c (qmul v v))
  exact bound_congr exactDiff.eqSymm (by dsimp only [rationalGain,f,j,g,l]; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ hBBB second scaled)

private theorem mercator_budget (A B : PTm n) (h : Γ ⊢[PRAAx] le (num 4*A) B) : Γ ⊢[PRAAx]
    le (mercNum A*(B*B*B)) (((A*A)*A)*mercDen A B) := by
  let d := monus B A
  let b := monus B (num 4*A)
  have aB : Γ ⊢[PRAAx] le A B := le_trans (le_of_eq_add (d := num 3*A) (by ipra_ring)) h
  have B1 : Γ ⊢[PRAAx] B ≐ A+d := eq_add_of_le aB
  have B2 : Γ ⊢[PRAAx] B ≐ num 4*A+b := eq_add_of_le h
  have hd : Γ ⊢[PRAAx] d ≐ num 3*A+b := add_left_cancel (a := A)
    (B1.eqSymm.eqTrans (B2.eqTrans (by ipra_ring)))
  have lift : Γ ⊢[PRAAx] num 3*(num 3*A+b) ≐ (num 4*A+b)+(num 5*A+two*b) := by ipra_ring
  have hD : Γ ⊢[PRAAx] le B (num 3*d) := le_of_eq_add (d := num 5*A+two*b)
    ((congrMul (.eqRefl _) hd).eqTrans (lift.eqTrans (congrAdd B2.eqSymm (.eqRefl _))))
  have ea : Γ ⊢[PRAAx] mercNum A ≐ (A*A)*A :=
    (pw_succ A two).eqTrans (congrMul (Common.pw_two A) (.eqRefl _))
  have eb : Γ ⊢[PRAAx] mercDen A B ≐ (num 3*d)*(B*B) :=
    congrMul (.eqRefl _) (Common.pw_two B)
  have k := mul_le_mul_right (((A*A)*A)*(B*B)) hD
  have e1 : Γ ⊢[PRAAx] mercNum A*(B*B*B) ≐ B*(((A*A)*A)*(B*B)) :=
    (congrMul ea (.eqRefl _)).eqTrans (by ipra_ring)
  have e2 : Γ ⊢[PRAAx] ((A*A)*A)*mercDen A B ≐ (num 3*d)*(((A*A)*A)*(B*B)) :=
    (congrMul (.eqRefl _) eb).eqTrans (by ipra_ring)
  exact le_congr e1.eqSymm e2.eqSymm k

theorem rate (z h R B H N M : PTm n) (hs : Γ ⊢[PRAAx] source z h R B H N M) : Γ ⊢[PRAAx]
    independentRate nameF constantF (data z h B N) (quadratic z h B N) (errorGain R N M*H*H*H) (B*B*B) := by
  let g := gain R N M
  let A := g*H
  let E := B*B*B
  let w := relative z h B N
  let v := Merc w
  let sz := numerator z h B N
  let rd := denominator z h B N
  let sr := radius z h B N
  let u := ofGaussian sz rd
  let x := data z h B N
  let y := quadratic z h B N
  have hi := hs.andE₁
  have hB := hi.andE₁
  have hE := positive_product _ _ (positive_product _ _ hB hB) hB
  have hm := hs.andE₂.andE₂.andE₁
  have hl := hs.andE₂.andE₂.andE₂.andE₁
  have h4 : Γ ⊢[PRAAx] le (num 4*A) B := hs.andE₂.andE₂.andE₂.andE₂
  have hz := source_of_small z h R B H N M hi hs.andE₂.andE₁ hm hl h4
  have hLocal := GaussianBarnesCanonicalHeadRelativeLog.local_source z h B N hz
  have hh : Γ ⊢[PRAAx] le (two*A) B :=
    le_trans (le_of_eq_add (d := two*A) (by ipra_ring)) h4
  have hAB := GaussianLocalLogarithmTaylorRemainder.half_disk_radius_strict A B hB hh
  have hD := GaussianFiniteLogarithmTaylorRemainder.denominator_positive A B two hB hAB
  have eu : Γ ⊢[PRAAx] u ≐ w := GaussianBarnesCanonicalHeadRelativeLog.decoded z h B N
  have hw : Γ ⊢[PRAAx] bounded u A B := bound_congr eu.eqSymm (.eqRefl _) (.eqRefl _)
    (relative_bound z h R B H N M hi hs.andE₂.andE₁ hm hl)
  have base := GaussianLocalLogarithmQuadraticRate.rate_at_radius sz sr rd A B hLocal hB hAB hw
  have mv : Γ ⊢[PRAAx] v ≐ Merc u := by
    exact qadd_congr eu.eqSymm (qmul_congr (.eqRefl _) (qmul_congr eu.eqSymm eu.eqSymm))
  have ret := GaussianNamedRateTransport.transport nameF constantF nameF constantF x (Merc u) x v (mercNum A) (mercDen A B)
    hD base (GaussianNameEquivalence.cross_refl _ _ (GaussianBarnesCanonicalHeadRelativeLog.regular z h B N hz))
    (GaussianGammaWeierstrassApproximant.constant_data_cross v (Merc u) mv)
  have cut := GaussianNamedRateRadius.weaken nameF constantF x v (mercNum A) (mercDen A B) ((A*A)*A) E hD hE
    (mercator_budget A B h4) ret
  have rat := GaussianNamedAddRate.constant_rate v y (rationalGain R N M*H*H*H) E hE (rational_error z h R B H N M hs)
  have sum := GaussianNamedRateComposition.same_denominator nameF constantF constantF x v y _ E _ hE cut rat
  exact rate_parameters_congr _ _ _ _ _ _ _ _
    (by dsimp only [A,g,errorGain]; ipra_ring) (.eqRefl _) sum

theorem actual_Barnes_kept_logarithm_cubic_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      independentRate nameF constantF (data (var 0) (var 1) (var 3) (var 5))
        (quadratic (var 0) (var 1) (var 3) (var 5)) (errorGain (var 2) (var 5) (var 6)*var 4*var 4*var 4)
        (var 3*var 3*var 3)) :=
  closeUniv 7 (.impI (rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadRelativeLogTaylor
