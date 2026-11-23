import IPRADerivations.Analysis.GaussianEulerPowerExponentialShift
import IPRADerivations.Analysis.GaussianRationalCoefficientScaling

/-!
# First-order remainder of the original Euler power

For the actual power of positive rational time, the exact linear term
at the earlier original observation is its product with
`(z/B-1)*c/a`. Its quadratic error is uniform on the compact time
interval. A later observation at precision p and an earlier observation
at precision q contribute `2^-p+5*2^-q`. All arithmetic uses the original
power and exponential product clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerIncrement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerShiftRate (source displaced_difference)
open GaussianEulerPowerExponentIncrement (linear)
open GaussianEulerPowerExponentialShift (relativeF relativeData productF productData relative_linear_remainder original_power_product_rate)
open GaussianEulerIntegrandName (powerExponentF powerExponentData powerF powerData powerRadius)
open GaussianEulerCompactPowerMajorant (majorant original_power_observation)
open GaussianRationalHorner (qadd qmul qmul_canonical positive_product)
open GaussianRationalSyntheticDivision (qone qadd_congr qsub_congr)
open GaussianRationalMetric (bounded qsub distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_sum qone_bounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def point (p z B a b : PTm n) : PTm n := ap2 powerF p (powerData z B a b)
def productClock (p z B a b c : PTm n) : PTm n :=
  GaussianFastValueCut.exponent (GaussianNameArithmetic.multiplyModulus powerF relativeF
    (powerData z B a b) (relativeData z B a c)) p
def linearFactor (z B a c : PTm n) : PTm n := qadd qone (linear z B a c)
def slopeTerm (q z B a b c : PTm n) : PTm n := qmul (point q z B a b) (linear z B a c)
def increment (p q z B a b c : PTm n) : PTm n := qsub (point p z B (a+c) b) (point q z B a b)
def productRemainder (R E T c : PTm n) : PTm n := majorant R E T*(((R+one)*c)*((R+one)*c))
def curvature (R E T c : PTm n) : PTm n := GaussianEulerPowerExponentialShift.coefficient R E T c+productRemainder R E T c
def remainderNumerator (p q R E T a c : PTm n) : PTm n :=
  curvature R E T c*(unit p*unit q)+(unit q+num 5*unit p)*(a*a)
def remainderDenominator (p q a : PTm n) : PTm n := (a*a)*(unit p*unit q)
def compactNumerator (p q R E T b c : PTm n) : PTm n :=
  (E*E)*curvature R E T c*(unit p*unit q)+(unit q+num 5*unit p)*(b*b)

theorem product_at (q z B a b c : PTm n) :
    Γ ⊢[PRAAx] ap2 productF q (productData z B a b c) ≐
      qmul (point (productClock q z B a b c) z B a b) (ap2 relativeF (productClock q z B a b c) (relativeData z B a c)) :=
  (GaussianNameArithmetic.multiply_at powerF relativeF (powerData z B a b) (relativeData z B a c) q).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))

theorem linear_factor_bound (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] bounded (linearFactor z B a c) two one := by
  have sum := bounded_sum qone (linear z B a c) one one one one (le_refl _) (le_refl _)
    (qone_bounded (Γ := Γ)) (GaussianEulerPowerShiftRate.unit_bound z R B E T a b c h)
  exact bound_congr (.eqRefl _) (by ipra_ring) (one_mul one) sum

theorem product_linear (q z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] distanceBounded (ap2 productF q (productData z B a b c))
      (qmul (point q z B a b) (linearFactor z B a c))
      (productRemainder R E T c*unit q+num 4*(a*a)) ((a*a)*unit q) := by
  let s := productClock q z B a b c
  let U := unit q
  let V := unit s
  let A := a*a
  let X := point s z B a b
  let Y := point q z B a b
  let D := linearFactor z B a c
  let L := majorant R E T
  let Z := ap2 relativeF s (relativeData z B a c)
  have hA := positive_product a a h.andE₂.andE₁.andE₁.andE₁ h.andE₂.andE₁.andE₁.andE₁
  have hU := unit_positive (Γ := Γ) q
  have hV := unit_positive (Γ := Γ) s
  have bX := original_power_observation s z R B E T a b h.andE₁ h.andE₂.andE₁
  have bY := original_power_observation q z R B E T a b h.andE₁ h.andE₂.andE₁
  have raw := bounded_product X (qsub Z D) L one (((R+one)*c)*((R+one)*c)) A
    (le_refl _) hA bX (relative_linear_remainder s z R B E T a b c h)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 productF q (productData z B a b c)) (qmul X D)
      (productRemainder R E T c) A := by
    have near : Γ ⊢[PRAAx] distanceBounded (qmul X Z) (qmul X D) (productRemainder R E T c) A :=
      bound_congr (GaussianRationalRoundedPower.multiplication_difference X Z D).eqSymm (.eqRefl _)
        (by ipra_ring) raw
    exact distance_congr (product_at q z B a b c).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) near
  have reg := GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁)
  have sampled : Γ ⊢[PRAAx] distanceBounded X Y (V+U) (V*U) :=
    GaussianNameEquivalence.point_at powerF (powerData z B a b) s q reg
  have later : Γ ⊢[PRAAx] le q s := le_add_right _ _
  have order : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone later
  have cmp : Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)) := by
    ipra_le 𝔞 U*sl order
  have normalized := distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hV hU) hU cmp sampled
  have changed := GaussianNameRingLaws.product_left_error X Y D two U two L hU normalized
    (linear_factor_bound z R B E T a b c h) bY
  have second : Γ ⊢[PRAAx] distanceBounded (qmul X D) (qmul Y D) (num 4) U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) changed
  exact GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hA hU first second

theorem original_power_increment (p q z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] distanceBounded (increment p q z B a b c) (slopeTerm q z B a b c)
      (remainderNumerator p q R E T a c) (remainderDenominator p q a) := by
  let P := unit p
  let Q := unit q
  let A := a*a
  let V := remainderDenominator p q a
  let X := point p z B (a+c) b
  let Y := point q z B a b
  let d := linear z B a c
  let C := GaussianEulerPowerExponentialShift.coefficient R E T c
  let W := ap2 productF q (productData z B a b c)
  have haa := positive_product a a h.andE₂.andE₁.andE₁.andE₁ h.andE₂.andE₁.andE₁.andE₁
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ haa (positive_product _ _ hp hq)
  have original := GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_power_product_rate z R B E T a b c h)
  have productObs : Γ ⊢[PRAAx] distanceBounded X W (C*(P*Q)+(P+Q)*A) V :=
    distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [C,P,Q,A,rateNumerator]; ipra_ring)
      (by dsimp only [V,P,Q,A,rateDenominator,remainderDenominator]; ipra_ring) original
  have nearby := product_linear q z R B E T a b c h
  have enlarged := distance_radius_mono _ _ _ _
    ((productRemainder R E T c*Q+num 4*A)*P) V (positive_product _ _ haa hq) hv
    (le_of_eq_add (d := zero) (by dsimp only [V,remainderDenominator,A,P,Q]; ipra_ring)) nearby
  have near := distance_triangle_same X W (qmul Y (linearFactor z B a c)) _ _ V hv productObs enlarged
  have canonical : Γ ⊢[PRAAx] GaussianRationalHorner.canonical Y :=
    GaussianRadiusExponentialName.sample_canonical powerExponentF (powerRadius z B a b) q (powerExponentData z B a b)
  have mulEq : Γ ⊢[PRAAx] qmul Y (linearFactor z B a c) ≐ qadd Y (qmul Y d) :=
    (GaussianRationalCoefficientScaling.qmul_add Y qone d).eqTrans
      (qadd_congr (GaussianReciprocalHorner.qmul_one_right Y canonical) (.eqRefl _))
  have diff : Γ ⊢[PRAAx] qsub X (qmul Y (linearFactor z B a c)) ≐ qsub (increment p q z B a b c) (slopeTerm q z B a b c) :=
    (qsub_congr (.eqRefl _) mulEq).eqTrans (displaced_difference _ _ _ (qmul_canonical _ _)).eqSymm
  exact bound_congr diff (by dsimp only [remainderNumerator,curvature,C,P,Q,A]; ipra_ring)
    (.eqRefl _) near

theorem original_Euler_power_first_order_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (increment (var 0) (var 1) (var 2) (var 4) (var 7) (var 8) (var 9))
        (slopeTerm (var 1) (var 2) (var 4) (var 7) (var 8) (var 9))
        (remainderNumerator (var 0) (var 1) (var 3) (var 5) (var 6) (var 7) (var 9))
        (remainderDenominator (var 0) (var 1) (var 7))) :=
  closeUniv 10 (.impI (original_power_increment _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem compact_power_increment (p q z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] distanceBounded (increment p q z B a b c) (slopeTerm q z B a b c)
      (compactNumerator p q R E T b c) (remainderDenominator p q b) := by
  let P := unit p
  let Q := unit q
  let K := curvature R E T c
  have ha := h.andE₂.andE₁.andE₁.andE₁
  have hb := h.andE₂.andE₁.andE₁.andE₂
  have pq : Γ ⊢[PRAAx] le one (P*Q) := positive_product _ _ (unit_positive p) (unit_positive q)
  have square := sq_le_sq h.andE₂.andE₁.andE₂.andE₁
  have compare : Γ ⊢[PRAAx] le (remainderNumerator p q R E T a c*remainderDenominator p q b)
      (compactNumerator p q R E T b c*remainderDenominator p q a) := by
    change Γ ⊢[PRAAx] le ((K*(P*Q)+(Q+num 5*P)*(a*a))*((b*b)*(P*Q)))
      (((E*E)*K*(P*Q)+(Q+num 5*P)*(b*b))*((a*a)*(P*Q)))
    ipra_le (𝔞 K*𝔞 P*𝔞 P*𝔞 Q*𝔞 Q)*sl square
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ ha ha) pq)
    (positive_product _ _ (positive_product _ _ hb hb) pq) compare (original_power_increment p q z R B E T a b c h)

theorem original_Euler_power_compact_step_remainder_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (increment (var 0) (var 1) (var 2) (var 4) (var 7) (var 8) (var 9))
        (slopeTerm (var 1) (var 2) (var 4) (var 7) (var 8) (var 9))
        (compactNumerator (var 0) (var 1) (var 3) (var 5) (var 6) (var 8) (var 9))
        (remainderDenominator (var 0) (var 1) (var 8))) :=
  closeUniv 10 (.impI (compact_power_increment _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerIncrement
