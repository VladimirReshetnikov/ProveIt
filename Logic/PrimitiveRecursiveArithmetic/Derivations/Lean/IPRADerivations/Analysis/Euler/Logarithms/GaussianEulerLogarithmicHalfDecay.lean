import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerWeightedHalfDecay
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianUpperTimeLogarithmPower

/-!
# Actual logarithmic powers and the first half-decay factor

The original power and original logarithm are observed at the same
precision. Their literal product has the sharp leading time monomial
of degree R+j. An arbitrary numerical observation allowance can then
be multiplied by the actual half-decay sample without enlarging the
factorial leading constant. All remaining losses are explicit dyadic
allowances; no limiting or integrability assertion is used here.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicHalfDecay

open_ipra
open GaussianEulerIntegrandName (powerF powerData)
open GaussianEulerUpperPowerOrder (source)
open GaussianEulerWeightedHalfDecay (majorant slack halfSample)
open GaussianUpperTimeLogarithmPower (rawPower gain)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def powerAndLog (p j z B a b : PTm n) : PTm n :=
  qmul (ap2 powerF p (powerData z B a b)) (rawPower p j a b)
def powerAllowance (j R a : PTm n) : PTm n :=
  pw a R*gain j a+pw a j+gain j a
def halfAllowance (a d K : PTm n) : PTm n :=
  K*majorant d+(K+one)*slack a d
def weightedSample (p j z B a b : PTm n) : PTm n :=
  qmul (powerAndLog p j z B a b) (halfSample p a b)
def observationClock (p j R a : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (halfAllowance a (R+j) (powerAllowance j R a)) p
def sampledHalfRow (p j z R B a b : PTm n) : PTm n :=
  weightedSample (observationClock p j R a) j z B a b

ipra_subst powerAndLog
ipra_subst powerAllowance
ipra_subst halfAllowance [slack]
ipra_subst weightedSample
ipra_subst observationClock
ipra_subst sampledHalfRow

/-- Product arithmetic retains the leading exact rational monomial. -/
theorem amplified_product (u v A B C D G U : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U)
    (hu : Γ ⊢[PRAAx] bounded u (A*U+B) (B*U))
    (hv : Γ ⊢[PRAAx] bounded v (C*U+G*D) (D*U)) :
    Γ ⊢[PRAAx] bounded (qmul u v) (A*C*U+(A*G+C+G)*B*D) (B*D*U) := by
  have bu := positive_product _ _ hB hU
  have du := positive_product _ _ hD hU
  have actual := bounded_product u v _ _ _ _ bu du hu hv
  have compare : Γ ⊢[PRAAx] le ((A*U+B)*(C*U+G*D))
      ((A*C*U+(A*G+C+G)*B*D)*U) := by
    ipra_le (𝔞 A*𝔞 G*𝔞 D*𝔞 U)*sl hB+
      (𝔞 B*𝔞 C*𝔞 U)*sl hD+(𝔞 B*𝔞 G*𝔞 D)*sl hU
  have reorder : Γ ⊢[PRAAx] ((A*C*U+(A*G+C+G)*B*D)*U)*(B*D*U) ≐
      (A*C*U+(A*G+C+G)*B*D)*((B*U)*(D*U)) := by ipra_ring
  have cross : Γ ⊢[PRAAx] le (((A*U+B)*(C*U+G*D))*(B*D*U))
      ((A*C*U+(A*G+C+G)*B*D)*((B*U)*(D*U))) :=
    le_congr (.eqRefl _) reorder (mul_le_mul_right (B*D*U) compare)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ bu du)
    (positive_product _ _ (positive_product _ _ hB hD) hU) cross actual

/-- The coefficient uses the unchanged original logarithm observation. -/
theorem original_power_and_log_bound (p j z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) :
    Γ ⊢[PRAAx] bounded (powerAndLog p j z B a b)
      (pw a (R+j)*unit p+powerAllowance j R a*pw b (R+j)) (pw b (R+j)*unit p) := by
  have bR := GaussianPolynomialPerturbation.power_positive b R h.andE₂.andE₁.andE₂
  have bj := GaussianPolynomialPerturbation.power_positive b j h.andE₂.andE₁.andE₂
  have actual := amplified_product (ap2 powerF p (powerData z B a b)) (rawPower p j a b)
    (pw a R) (pw b R) (pw a j) (pw b j) (gain j a) (unit p) bR bj (unit_positive p)
    (GaussianEulerUpperPowerBound.original_power_bound p z R B a b h)
    (GaussianUpperTimeLogarithmPower.original_power_bound p j a b h.andE₂.andE₁ h.andE₂.andE₂)
  have numerator : Γ ⊢[PRAAx]
      pw a R*pw a j*unit p+(pw a R*gain j a+pw a j+gain j a)*pw b R*pw b j ≐
        pw a (R+j)*unit p+powerAllowance j R a*pw b (R+j) :=
    (by unfold powerAllowance; ipra_ring : Γ ⊢[PRAAx] _ ≐
      (pw a R*pw a j)*unit p+powerAllowance j R a*(pw b R*pw b j)).eqTrans
      (congrAdd (congrMul (pw_add a R j).eqSymm (.eqRefl _))
        (congrMul (.eqRefl _) (pw_add b R j).eqSymm))
  have denominator : Γ ⊢[PRAAx] pw b R*pw b j*unit p ≐ pw b (R+j)*unit p :=
    congrMul (pw_add b R j).eqSymm (.eqRefl _)
  exact bound_congr (.eqRefl _) numerator denominator actual

/-- An arbitrary allowance K changes only the dyadic remainder. -/
theorem amplified_weighted_half_decay (q p a b d K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hab : Γ ⊢[PRAAx] le b a)
    (hq : Γ ⊢[PRAAx] bounded q (pw a d*unit p+K*pw b d) (pw b d*unit p)) :
    Γ ⊢[PRAAx] bounded (qmul q (halfSample p a b))
      (majorant d*unit p+halfAllowance a d K) (unit p) := by
  let A := pw a d
  let B := pw b d
  let U := unit p
  let M := majorant d
  let S := slack a d
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have ha := le_trans hb hab
  have hA : Γ ⊢[PRAAx] le one A := GaussianPolynomialPerturbation.power_positive a d ha
  have hB : Γ ⊢[PRAAx] le one B := GaussianPolynomialPerturbation.power_positive b d hb
  have bu := positive_product _ _ hB hu
  have ua := positive_product _ _ hu hA
  have actual := bounded_product q (halfSample p a b) _ _ _ _ bu ua hq
    (GaussianEulerWeightedHalfDecay.half_decay_monomial_bound p a b d ha hb)
  have first : Γ ⊢[PRAAx] le (A*U+K*B) (A*U+K*A) :=
    add_le_add₂ (le_refl (A*U))
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right K (pw_le_pw d hab)))
  have second : Γ ⊢[PRAAx] le ((A*U+K*A)*(M*U+S))
      (A*U*(M*U+K*M+(K+one)*S)) := by
    ipra_le (𝔞 A*𝔞 K*𝔞 S)*sl hu
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ bu ua) hu _ actual
  exact le_congr (by ipra_ring) (by unfold halfAllowance; dsimp only [A,B,U,M,S]; ipra_ring)
    (mul_le_mul_right (B*U)
      (le_trans (mul_le_mul_right (M*U+S) first) second))

/-- Source-only first-half bound for the actual raw logarithmic row. -/
theorem original_weighted_half_decay_bound (p j z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) :
    Γ ⊢[PRAAx] bounded (weightedSample p j z B a b)
      (majorant (R+j)*unit p+halfAllowance a (R+j) (powerAllowance j R a)) (unit p) :=
  amplified_weighted_half_decay (powerAndLog p j z B a b) p a b (R+j) (powerAllowance j R a)
    h.andE₂.andE₁.andE₂ h.andE₂.andE₂ (original_power_and_log_bound p j z R B a b h)

/-- A computed numerical clock pays every proved allowance. The leading
factorial majorant is unchanged and the output uses the actual raw row. -/
theorem original_sampled_half_row_bound (p j z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B a b) :
    Γ ⊢[PRAAx] bounded (sampledHalfRow p j z R B a b)
      (majorant (R+j)*unit p+one) (unit p) := by
  let s := observationClock p j R a
  let K := halfAllowance a (R+j) (powerAllowance j R a)
  have query : Γ ⊢[PRAAx] le (K*unit p) (unit s) := GaussianFastValueCut.query_budget K p
  have compare : Γ ⊢[PRAAx] le ((majorant (R+j)*unit s+K)*unit p)
      ((majorant (R+j)*unit p+one)*unit s) := by ipra_le sl query
  exact bounded_radius_mono _ _ _ _ _ (unit_positive s) (unit_positive p) compare
    (original_weighted_half_decay_bound s j z R B a b h)

theorem actual_amplified_weighted_half_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 3) ⟶ le (var 3) (var 2) ⟶
      bounded (var 0) (pw (var 2) (var 4)*unit (var 1)+var 5*pw (var 3) (var 4))
        (pw (var 3) (var 4)*unit (var 1)) ⟶
      bounded (qmul (var 0) (halfSample (var 1) (var 2) (var 3)))
        (majorant (var 4)*unit (var 1)+halfAllowance (var 2) (var 4) (var 5)) (unit (var 1))) :=
  closeUniv 6 (.impI (.impI (.impI (amplified_weighted_half_decay _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem original_logarithmic_weighted_half_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (weightedSample (var 0) (var 1) (var 2) (var 4) (var 5) (var 6))
        (majorant (var 3+var 1)*unit (var 0)+
          halfAllowance (var 5) (var 3+var 1) (powerAllowance (var 1) (var 3) (var 5))) (unit (var 0))) :=
  closeUniv 7 (.impI (original_weighted_half_decay_bound _ _ _ _ _ _ _ Prf.hyp0))

theorem original_logarithmic_sampled_half_row_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      bounded (sampledHalfRow (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
        (majorant (var 3+var 1)*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 7 (.impI (original_sampled_half_row_bound _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicHalfDecay
