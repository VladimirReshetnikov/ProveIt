import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridBudget
import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridReadback

/-!
# A quadratic rate for the literal finite Barnes even grid

Two original finite observation grids converge to the doubled
factorial coefficient at a quadratic rate on each disk. The grid and
polynomial clocks pay their own numerical costs. The final name may
be read at any independent observation clock.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq bounded_mono)
open GaussianBarnesCanonicalFiniteTaylorEvenGridBudget (analyticCoefficient clockCoefficient observationCoefficient)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (observed target)
open GaussianBarnesCanonicalFiniteTaylorEvenGridReadback (observationCost prefactorClock)
open GaussianBarnesCanonicalFixedTaylorDerivativeName (readbackGain)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1 normSq_le_norm1_square norm1_square_le_two_normSq)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalNaturalScale (natScale)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def stepCost (R M e : PTm n) : PTm n := e*stepDivisor R+analyticCoefficient R M e

def stepClock (p R M e : PTm n) : PTm n := exponent (stepCost R M e) p

def coefficientClock (p z R B e : PTm n) : PTm n :=
  exponent (num 3*(two*readbackGain z (R+one) B e)) p

def polynomialClock (p z R B M e : PTm n) : PTm n :=
  prefactorClock (coefficientClock p z R B e) z R B M e+exponent (num 3*clockCoefficient R B e) p

def observationClock (p z h R B r M e : PTm n) : PTm n :=
  let q := polynomialClock p z R B M e
  let H := norm1 h
  exponent (num 3*(observationCoefficient q z h R B H r M e+two*(one+observationCost q z R B H r M e))) p

def quadraticNumerator (p u R B H M e : PTm n) : PTm n :=
  analyticCoefficient R M e*(H*H)*unit p*unit u+(B*B)*(unit u+two*unit p)

def quadraticDenominator (p u B : PTm n) : PTm n := (B*B)*unit p*unit u

def quadraticClock (B : PTm n) : PTm n := exponent (B*B) zero

def uniformGain (R M e : PTm n) : PTm n := analyticCoefficient R M e+num 3

theorem quadratic_denominator_positive (p u B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] le one (quadraticDenominator p u B) :=
  positive_product _ _ (positive_product _ _ (positive_product B B hb hb) (unit_positive p)) (unit_positive u)

theorem disk_threshold (p h R B M e : PTm n)
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R M e)) B) :
    Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B ⋏
      le (analyticCoefficient R M e*(norm1 h*norm1 h)*unit p) (B*B) := by
  let H := norm1 h
  let A := analyticCoefficient R M e
  let C := stepCost R M e
  let P := unit p
  let W := unit (stepClock p R M e)
  have pay : Γ ⊢[PRAAx] le (C*P) W := query_budget C p
  have admission_le_cost : Γ ⊢[PRAAx] le (e*stepDivisor R) C := le_add_right _ _
  have analytic_le_cost : Γ ⊢[PRAAx] le A C := le_add_left _ _
  have grow : Γ ⊢[PRAAx] le C (C*P) :=
    le_congr (one_mul C) (mul_comm _ _) (mul_le_mul_right C (unit_positive p))
  have admitted : Γ ⊢[PRAAx] le ((e*stepDivisor R)*H) B :=
    le_trans (le_congr (.eqRefl _) (mul_comm _ _)
      (mul_le_mul_right H (le_trans admission_le_cost (le_trans grow pay)))) hs
  have scaled : Γ ⊢[PRAAx] le ((A*P)*H) B :=
    le_trans (le_congr (.eqRefl _) (mul_comm _ _)
      (mul_le_mul_right H (le_trans (mul_le_mul_right P analytic_le_cost) pay))) hs
  have hB : Γ ⊢[PRAAx] le H B :=
    le_trans (le_congr (one_mul H) (mul_comm _ _) (mul_le_mul_right H (unit_positive (stepClock p R M e)))) hs
  exact .andI admitted (le_congr (by ipra_ring) (.eqRefl _) (Common.mul_le_mul scaled hB))

private theorem native_lower (h B : PTm n) (hb : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ofGaussian h B) (norm1 h) (two*B) := by
  apply lower_from_representation _ h B _ _ hb (positive_product _ _ (le_succ_self one) hb)
    (ofGaussian_represents h B hb)
  have hsq := norm1_square_le_two_normSq (Γ := Γ) h
  ipra_le 𝔞(B)*𝔞(B)*(sl hsq+2*𝔞(normSq h))

private theorem budget_sum (U V B Q T W a c d f g : PTm n)
    (hc : Γ ⊢[PRAAx] le (num 3*U*c) Q)
    (ht : Γ ⊢[PRAAx] le (num 3*U*(d+two*(one+f))) T)
    (hg : Γ ⊢[PRAAx] le (num 3*U*(two*g)) W) :
    let A := a*Q*T+c*B*T+d*B*Q
    let J := two*(g*V*T+W*(V+T)+f*W*V)
    let X := B*Q*T
    let Y := W*V*T
    Γ ⊢[PRAAx] le ((A*Y+J*X)*(B*U*V)) ((a*U*V+B*(V+two*U))*(X*Y)) := by
  dsimp only
  apply Common.mul_cancel_le (show Γ ⊢[PRAAx] le one (num 3) from zero_lt_succ _)
  ipra_le (𝔞(B)*𝔞(B)*𝔞(V)*𝔞(V)*𝔞(W)*𝔞(T)*𝔞(T))*sl hc+
    (𝔞(B)*𝔞(B)*𝔞(V)*𝔞(V)*𝔞(W)*𝔞(Q)*𝔞(T))*sl ht+
    (𝔞(B)*𝔞(B)*𝔞(V)*𝔞(V)*𝔞(Q)*𝔞(T)*𝔞(T))*sl hg

theorem quadratic_rate (p z h R B r M J e t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock p z h R B r M e) t) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
      (quadraticNumerator p u R B (norm1 h) M e) (quadraticDenominator p u B) := by
  let H := norm1 h
  let S := R+one
  let k := coefficientClock p z R B e
  let q := polynomialClock p z R B M e
  let C := clockCoefficient R B e
  let K := observationCoefficient q z h R B H r M e
  let L := observationCost q z R B H r M e
  let G := readbackGain z S B e
  let A := GaussianBarnesCanonicalFiniteTaylorEvenGridBudget.numerator q t z h R B H r M e
  let X := GaussianBarnesCanonicalFiniteTaylorEvenGridBudget.denominator q t B
  let Y := rateDenominator (unit k) u t
  let C' := GaussianBarnesCanonicalFiniteTaylorEvenGridReadback.numerator u t k q z R B H r M e
  let x := observed t z h R B r e
  let y := target t q z R B H r M e
  let v := natScale two (ap2 F u (fd z S B r J e))
  have hb := hz.andE₁
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have enlarged : Γ ⊢[PRAAx] source z S B :=
    .andI hb (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by dsimp only [S]; ipra_ring)))
  have hX : Γ ⊢[PRAAx] le one X := GaussianBarnesCanonicalFiniteTaylorEvenGridBudget.denominator_positive q t B hb
  have hY : Γ ⊢[PRAAx] le one Y := GaussianNamedInverseRate.denominator_positive _ _ _ (unit_positive k)
  have whole := positive_product X Y hX hY
  have hf : Γ ⊢[PRAAx] le (prefactorClock k z R B M e) q := le_add_right _ _
  have fromGrid : Γ ⊢[PRAAx] distanceBounded x y A X :=
    GaussianBarnesCanonicalFiniteTaylorEvenGridBudget.coefficient_error q t z h R B H r M e
      hz (normSq_le_norm1_square h) hsmall hH hdeg (native_lower h B hb)
  have fromCoeff : Γ ⊢[PRAAx] distanceBounded y v C' Y :=
    GaussianBarnesCanonicalFiniteTaylorEvenGridReadback.readback u t k q z R B H r M J e enlarged hdeg hJ hf
  have first : Γ ⊢[PRAAx] distanceBounded x y (A*Y) (X*Y) :=
    distance_radius_mono _ _ _ _ _ _ hX whole (le_of_eq_add (d := zero) (by ipra_ring)) fromGrid
  have next : Γ ⊢[PRAAx] distanceBounded y v (C'*X) (X*Y) :=
    distance_radius_mono _ _ _ _ _ _ hY whole (le_of_eq_add (d := zero) (by ipra_ring)) fromCoeff
  have payCoeff : Γ ⊢[PRAAx] le (num 3*unit p*(two*G)) (unit k) :=
    le_congr (by ipra_ring) (.eqRefl _) (query_budget (num 3*(two*G)) p)
  have payTaylor : Γ ⊢[PRAAx] le (num 3*unit p*C) (unit q) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (query_budget (num 3*C) p))
      (unit_monotone (le_add_left _ _))
  have payObs : Γ ⊢[PRAAx] le (num 3*unit p*(K+two*(one+L))) (unit t) :=
    le_trans (le_congr (by ipra_ring) (.eqRefl _) (query_budget (num 3*(K+two*(one+L))) p)) (unit_monotone ht)
  exact distance_radius_mono _ _ _ _ _ _ whole (quadratic_denominator_positive p u B hb)
    (budget_sum (unit p) (unit u) (B*B) (unit q) (unit t) (unit k)
      (analyticCoefficient R M e*(H*H)) C K L G payTaylor payObs payCoeff)
    (distance_triangle_same _ _ _ _ _ _ whole first next)

theorem uniform_rate (z h R B r M J e t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock (quadraticClock B) z h R B r M e) t)
    (hu : Γ ⊢[PRAAx] le (quadraticClock B) u) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
      (uniformGain R M e*(norm1 h*norm1 h)) (B*B) := by
  let p := quadraticClock B
  let U := unit p
  let V := unit u
  let b := B*B
  let H := norm1 h
  let A := analyticCoefficient R M e
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hs : Γ ⊢[PRAAx] le one (H*H) := positive_product H H hH hH
  have fit : Γ ⊢[PRAAx] b*unit zero ≐ b :=
    (congrMul (.eqRefl _) (pw_zero two)).eqTrans (by ipra_ring)
  have hp : Γ ⊢[PRAAx] le b U := le_congr fit (.eqRefl _) (query_budget b zero)
  have hv : Γ ⊢[PRAAx] le b V := le_trans hp (unit_monotone hu)
  have cmp : Γ ⊢[PRAAx] le
      ((A*(H*H)*U*V+b*(V+two*U))*b) (((A+num 3)*(H*H))*(b*U*V)) := by
    ipra_le (𝔞(b)*𝔞(V))*sl hp+(2*𝔞(b)*𝔞(U))*sl hv+(3*𝔞(b)*𝔞(U)*𝔞(V))*sl hs
  exact distance_radius_mono _ _ _ _ _ _
    (quadratic_denominator_positive p u B hz.andE₁) (positive_product B B hz.andE₁ hz.andE₁) cmp
    (quadratic_rate p z h R B r M J e t u hz hn hsmall hdeg hJ ht)

theorem disk_rate (p z h R B r M J e t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R M e)) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock p z h R B r M e) t) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
      (two*unit u+two*unit p) (unit p*unit u) := by
  have cert := disk_threshold p h R B M e hs
  let H := norm1 h
  let A := analyticCoefficient R M e
  let U := unit p
  let V := unit u
  have cmp : Γ ⊢[PRAAx] le ((A*(H*H)*U*V+(B*B)*(V+two*U))*(U*V))
      ((two*V+two*U)*((B*B)*U*V)) := by
    ipra_le (𝔞(U)*𝔞(V)*𝔞(V))*sl cert.andE₂
  exact distance_radius_mono _ _ _ _ _ _ (quadratic_denominator_positive p u B hz.andE₁)
    (positive_product U V (unit_positive p) (unit_positive u)) cmp
    (quadratic_rate p z h R B r M J e t u hz hn cert.andE₁ hdeg hJ ht)

theorem actual_Barnes_finite_even_disk_grid_limit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     let J := var 7
     let e := var 8
     let t := var 9
     let u := var 10
     (source z R B ⋏ (le one (normSq h) ⋏ (previous M ≐ succ e ⋏ le e (previous J)))) ⟶
       (le (norm1 h*unit (stepClock p R M e)) B ⋏ le (observationClock p z h R B r M e) t) ⟶
       distanceBounded (observed t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
         (two*unit u+two*unit p) (unit p*unit u)) :=
  closeUniv 11 (.impI (.impI (disk_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp0.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂ Prf.hyp0.andE₂)))

theorem actual_Barnes_finite_even_grid_uniform_quadratic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let J := var 6
     let e := var 7
     let t := var 8
     let u := var 9
     (source z R B ⋏ (le one (normSq h) ⋏ (previous M ≐ succ e ⋏ le e (previous J)))) ⟶
       (le ((e*stepDivisor R)*norm1 h) B ⋏ (le (observationClock (quadraticClock B) z h R B r M e) t ⋏
         le (quadraticClock B) u)) ⟶
       distanceBounded (observed t z h R B r e) (natScale two (ap2 F u (fd z (R+one) B r J e)))
         (uniformGain R M e*(norm1 h*norm1 h)) (B*B)) :=
  closeUniv 10 (.impI (.impI (uniform_rate (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp0.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorEvenGridLimit
