import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteWeightedTaylorValue
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Separate the finite Barnes Taylor remainder on the derivative grid

For a grid of order e, each node lies within e times the step bound.
The original finite Taylor rate at that radius has one term in the
step to degree e+1 and one term in the output clock. Both gains are
independent of the step and the actual finite tail cutoff.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridBudget

open_ipra
open ComplexLogarithmRemainder (add bounded)
open GaussianBarnesCanonicalCenteredProductRate (headCap)
open GaussianBarnesCanonicalCorrectedMercatorCofinal (analyticDenominator analytic_denominator_positive)
open GaussianBarnesCanonicalExponentTaylorWeightedMass (massCap)
open GaussianBarnesCanonicalFiniteCentralExponentialBound (centralCap)
open GaussianBarnesCanonicalFiniteExponentTaylor (scheduledDenominator)
open GaussianBarnesCanonicalFiniteWeightedTaylorValue (nameF data)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalTaylorRecomposition (capGain)
open GaussianBarnesCanonicalWeightedTaylorBall (headMass)
open GaussianBarnesCanonicalWeightedTaylorBallSource (input stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "V" => GaussianBarnesCanonicalValue.prefixF
local notation "literal" => GaussianBarnesCanonicalProduct.literalData

def clockGain (z R B : PTm n) : PTm n := headCap R*(centralCap z R B*capGain two)

def analyticGain (z R B M : PTm n) : PTm n :=
  let e := previous M
  let j := succ e
  let L := massCap R
  let E := pw (num 3) L
  clockGain z R B*(two*pw (two*e) j)+
    centralCap z R B*(headCap R*(two*pw L j+E)+headMass z R B*E)*pw (num 4*e) j

def numerator (q z R B H M : PTm n) : PTm n :=
  analyticGain z R B M*pw H (succ (previous M))*unit q+clockGain z R B*pw B (succ (previous M))

def denominator (q B M : PTm n) : PTm n := pw B (succ (previous M))*unit q

def clockGainWithCaps (R F : PTm n) : PTm n := headCap R*(F*capGain two)

def analyticGainWithCaps (R M P F : PTm n) : PTm n :=
  let e := previous M
  let j := succ e
  let L := massCap R
  let E := pw (num 3) L
  clockGainWithCaps R F*(two*pw (two*e) j)+
    F*(headCap R*(two*pw L j+E)+P*E)*pw (num 4*e) j

def numeratorWithCaps (q R B H M P F : PTm n) : PTm n :=
  analyticGainWithCaps R M P F*pw H (succ (previous M))*unit q+clockGainWithCaps R F*pw B (succ (previous M))

@[simp] theorem subst_clockGainWithCaps {l : ℕ} (σ : Fin n → PTm l) (R F : PTm n) :
    Syn.subst σ (clockGainWithCaps R F) = clockGainWithCaps (Syn.subst σ R) (Syn.subst σ F) := by
  simp [clockGainWithCaps,capGain,GaussianRadiusExponentialLipschitzRate.factor,
    GaussianNamedExponentialRateFromConstant.cap,one,two]

@[simp] theorem subst_analyticGainWithCaps {l : ℕ} (σ : Fin n → PTm l) (R M P F : PTm n) :
    Syn.subst σ (analyticGainWithCaps R M P F) = analyticGainWithCaps (Syn.subst σ R) (Syn.subst σ M)
      (Syn.subst σ P) (Syn.subst σ F) := by
  simp [analyticGainWithCaps,one,two]

@[simp] theorem subst_numeratorWithCaps {l : ℕ} (σ : Fin n → PTm l) (q R B H M P F : PTm n) :
    Syn.subst σ (numeratorWithCaps q R B H M P F) = numeratorWithCaps (Syn.subst σ q) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) (Syn.subst σ P) (Syn.subst σ F) := by simp [numeratorWithCaps]

@[simp] theorem subst_clockGain {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (clockGain z R B) = clockGain (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [clockGain,capGain,GaussianRadiusExponentialLipschitzRate.factor,GaussianNamedExponentialRateFromConstant.cap,one,two]

@[simp] theorem subst_analyticGain {l : ℕ} (σ : Fin n → PTm l) (z R B M : PTm n) :
    Syn.subst σ (analyticGain z R B M) = analyticGain (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ M) := by
  simp [analyticGain,headMass,GaussianRationalPolynomialExponentialRecomposition.coefficientBudget,
    GaussianBarnesCanonicalTaylorProduct.headPolynomial,GaussianBarnesCanonicalTaylorProduct.headDegree,
    RationalSupMetric.numeratorOf,one,two]

@[simp] theorem subst_numerator {l : ℕ} (σ : Fin n → PTm l) (q z R B H M : PTm n) :
    Syn.subst σ (numerator q z R B H M) = numerator (Syn.subst σ q) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ H) (Syn.subst σ M) := by simp [numerator]

@[simp] theorem subst_denominator {l : ℕ} (σ : Fin n → PTm l) (q B M : PTm n) :
    Syn.subst σ (denominator q B M) = denominator (Syn.subst σ q) (Syn.subst σ B) (Syn.subst σ M) := by simp [denominator]

private theorem grid_power (C H M : PTm n) : Γ ⊢[PRAAx]
    pw (C*(previous M*H)) (succ (previous M)) ≐ pw (C*previous M) (succ (previous M))*pw H (succ (previous M)) :=
  (congrAp2 powF (.eqRefl _) (by ipra_ring)).eqTrans
    (AnalyticNumberTheory.LocalFactor.pw_mul_base _ _ _)

private theorem analytic_denominator_room (R B M : PTm n) : Γ ⊢[PRAAx]
    le (pw B (succ (previous M))) (analyticDenominator (previous M) R B) := by
  let j := succ (previous M)
  let b := pw B j
  have first : Γ ⊢[PRAAx] le b (j*b) :=
    le_congr (one_mul b) (.eqRefl _) (mul_le_mul_right b (zero_lt_succ (previous M)))
  have second : Γ ⊢[PRAAx] le (j*b) ((j*b)*initial R) :=
    le_congr (one_mul (j*b)) (mul_comm (initial R) (j*b)) (mul_le_mul_right (j*b) (initial_positive R))
  exact le_trans first second

/-- The cross-multiplied comparison uses only the exact bound formulas.
In particular, it does not depend on a small-step or nonzero-step premise. -/
theorem radius_comparison_with_caps (q R B H M P F : PTm n) : Γ ⊢[PRAAx]
    le (GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator_with_caps q R B (previous M*H) M P F*denominator q B M)
      (numeratorWithCaps q R B H M P F*GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q R B M) := by
  let e := previous M
  let j := succ e
  let u := unit q
  let b := pw B j
  let d := analyticDenominator e R B
  let K := headCap R
  let c : PTm n := capGain two
  let L := massCap R
  let E := pw (num 3) L
  let t := pw H j
  let a := pw (two*e) j
  let v := pw (num 4*e) j
  have room : Γ ⊢[PRAAx] le b d := analytic_denominator_room R B M
  have p₂ := natEq (grid_power (Γ := Γ) two H M)
  have p₄ := natEq (grid_power (Γ := Γ) (num 4) H M)
  change Γ ⊢[PRAAx] le
    ((K*(F*((c*(two*pw (two*(e*H)) j*u+d))*b+((two*pw L j+E)*pw (num 4*(e*H)) j)*(d*u)))+
      (d*u)*(F*((P*E)*pw (num 4*(e*H)) j)))*(b*u))
    ((((K*(F*c)*(two*a)+F*(K*(two*pw L j+E)+P*E)*v)*t*u+K*(F*c)*b))*((d*u)*b))
  ipra_le (2*𝔞 K*𝔞 F*𝔞 c*𝔞 a*𝔞 t*𝔞 u*𝔞 u*𝔞 b)*sl room using
    rw [p₂,p₄]
    ring

theorem radius_comparison (q z R B H M : PTm n) : Γ ⊢[PRAAx]
    le (GaussianBarnesCanonicalFiniteWeightedTaylorValue.numerator q z R B (previous M*H) M*denominator q B M)
      (numerator q z R B H M*GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q R B M) :=
  radius_comparison_with_caps q R B H M (headMass z R B) (centralCap z R B)

theorem denominator_positive (q B M : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (denominator q B M) :=
  positive_product _ _ (GaussianFactorBudget.power_positive B (succ (previous M)) hb) (unit_positive q)

theorem rate (q z h R B H r M : PTm n) (hs : Γ ⊢[PRAAx] input z h R B (previous M*H) M) :
    Γ ⊢[PRAAx] independentRate V nameF (literal (add z h) R B (initial R+r))
      (data q z h R B (previous M*H) r M) (numerator q z R B H M) (denominator q B M) := by
  have hb := hs.andE₁.andE₁.andE₁
  have hd : Γ ⊢[PRAAx] le one (scheduledDenominator q R B M) :=
    positive_product _ _ (analytic_denominator_positive (previous M) R B hb) (unit_positive q)
  have original : Γ ⊢[PRAAx] le one (GaussianBarnesCanonicalFiniteWeightedTaylorValue.denominator q R B M) :=
    positive_product _ _ hd (GaussianFactorBudget.power_positive B (succ (previous M)) hb)
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ original (denominator_positive q B M hb)
    (radius_comparison q z R B H M) (GaussianBarnesCanonicalFiniteWeightedTaylorValue.rate q z h R B (previous M*H) r M hs)

theorem shared_rate (q z h R B H r M : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h (previous M*H)) (hs : Γ ⊢[PRAAx] le (stepDivisor R*(previous M*H)) B) :
    Γ ⊢[PRAAx] independentRate V nameF (literal (add z h) (R+one) B (initial (R+one)+r))
      (data q z h (R+one) B (previous M*H) r M) (numerator q z (R+one) B H M) (denominator q B M) :=
  rate q z h (R+one) B H r M (GaussianBarnesCanonicalWeightedTaylorBallSource.admission z h R B (previous M*H) M hz hh hs)

theorem actual_Barnes_finite_Taylor_grid_budget_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let q := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let H := var 5
     let r := var 6
     let M := var 7
     input z h R B (previous M*H) M ⟶
       independentRate V nameF (literal (add z h) R B (initial R+r)) (data q z h R B (previous M*H) r M)
         (numerator q z R B H M) (denominator q B M)) :=
  closeUniv 8 (.impI (rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridBudget
