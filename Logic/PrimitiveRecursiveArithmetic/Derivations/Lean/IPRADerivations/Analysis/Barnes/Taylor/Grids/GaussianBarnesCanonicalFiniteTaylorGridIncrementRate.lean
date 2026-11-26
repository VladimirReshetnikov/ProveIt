import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridWindows
import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalFiniteTaylorEvenGridLimit

/-!
# Fixed Barnes factorial quotient and the next mixed grid

Quadratic comparisons at both endpoints of the same finite product
yield a linear difference-quotient estimate after normalization.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridIncrementRate

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalFiniteTaylorEvenGridComparison (observed)
open GaussianBarnesCanonicalFiniteTaylorEvenGridLimit (quadraticClock uniformGain uniform_rate)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (deadline)
open GaussianBarnesCanonicalFiniteTaylorGridObservations (literalGrid)
open GaussianBarnesCanonicalFiniteTaylorMixedGridPolynomial (mixedGrid)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor stepDivisor_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (query_budget)
open GaussianL1 (norm1 norm1_square_le_two_normSq normSq_le_norm1_square)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble)
open GaussianPolynomialForwardDifferenceGridIncrement (slice)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul)
open GaussianRationalLowerBounds (lower lower_from_representation)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalReciprocal (reciprocal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

local notation "evenClock" => GaussianBarnesCanonicalFiniteTaylorEvenGridLimit.observationClock

def observationClock (z h R B r M e : PTm n) : PTm n :=
  let p := quadraticClock B
  deadline p B e+(evenClock p z h R B r M e+evenClock p (add z h) h R B r M e)

def numerator (R M e h : PTm n) : PTm n := two*(uniformGain R M e+(uniformGain R M e+one))*norm1 h

private theorem step_lower (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ofGaussian h B) (norm1 h) (two*B) := by
  apply lower_from_representation _ h B _ _ hB (positive_product _ _ (le_succ_self one) hB)
    (ofGaussian_represents h B hB)
  have hs := norm1_square_le_two_normSq (Γ := Γ) h
  ipra_le 𝔞(B)*𝔞(B)*(sl hs+2*𝔞(normSq h))

theorem rate (z h R B r M J e t u v : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock z h R B r M e) t)
    (hu : Γ ⊢[PRAAx] le (quadraticClock B) u) (hv : Γ ⊢[PRAAx] le (quadraticClock B) v) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (reciprocal (ofGaussian h B))
        (qsub (natScale two (ap2 F v (fd (add z h) (R+one) B r J e)))
          (natScale two (ap2 F u (fd z (R+one) B r J e))))) (mixedGrid t z h R B r e) (numerator R M e h) B := by
  let V := literalGrid t z h R B r (succ e)
  let W := literalGrid t (add z h) (gneg h) R B r (succ e)
  let H := norm1 h
  let Q := B*B
  let k := quadraticClock B
  let G := uniformGain R M e
  let q := ofGaussian h B
  let x := natScale two (ap2 F v (fd (add z h) (R+one) B r J e))
  let y := natScale two (ap2 F u (fd z (R+one) B r J e))
  let A := observedDouble (slice V one (succ e)) (slice W zero (succ e)) e q
  let C := observedDouble (slice V zero (succ e)) (slice W one (succ e)) e q
  let O := observed t z h R B r e
  have hB := hz.andE₁
  have hQ := positive_product B B hB hB
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hH₂ := positive_product H H hH hH
  have width : Γ ⊢[PRAAx] le (e*H) B := by
    have one_le := stepDivisor_positive (Γ := Γ) R
    have mono := mul_le_mul_right H (mul_le_mul_right e one_le)
    exact le_trans (le_congr (by ipra_ring) (by ipra_ring) mono) hsmall
  let Z := evenClock k z h R B r M e
  let Wclock := evenClock k (add z h) h R B r M e
  let K := deadline k B e
  have lateZ : Γ ⊢[PRAAx] le Z t := le_trans (le_add_right Z Wclock) (le_trans (le_add_left (Z+Wclock) K) ht)
  have lateW : Γ ⊢[PRAAx] le Wclock t := le_trans (le_add_left Wclock Z) (le_trans (le_add_left (Z+Wclock) K) ht)
  have lateK : Γ ⊢[PRAAx] le K t := le_trans (le_add_right K (Z+Wclock)) ht
  have left := uniform_rate (add z h) h R B r M J e t v hw hn hsmall hdeg hJ lateW hv
  have right := uniform_rate z h R B r M J e t u hz hn hsmall hdeg hJ lateZ hu
  have hx : Γ ⊢[PRAAx] distanceBounded x A (G*(H*H)) Q :=
    distance_congr (.eqRefl _) (GaussianBarnesCanonicalFiniteTaylorEvenGridWindows.shifted_equal t z h R B r e).eqSymm
      (.eqRefl _) (.eqRefl _) (distance_symmetric _ _ _ _ hQ left)
  have center := GaussianBarnesCanonicalFiniteTaylorEvenGridWindows.centered_rate k t z h R B H r e hz
    (normSq_le_norm1_square h) width hn lateK
  have paid : Γ ⊢[PRAAx] le Q (unit k) := le_congr
    ((congrMul (.eqRefl Q) (pw_zero two)).eqTrans (by ipra_ring)) (.eqRefl _) (query_budget Q zero)
  have fit : Γ ⊢[PRAAx] le (one*Q) ((H*H)*unit k) :=
    le_trans (le_congr (one_mul Q).eqSymm (one_mul (unit k)).eqSymm paid) (mul_le_mul_right (unit k) hH₂)
  have near : Γ ⊢[PRAAx] distanceBounded O C (H*H) Q :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive k) hQ fit center
  have hy : Γ ⊢[PRAAx] distanceBounded y C ((G+one)*(H*H)) Q :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same y O C _ _ Q hQ (distance_symmetric _ _ _ _ hQ right) near)
  exact GaussianPolynomialForwardDifferenceGridEvenIncrement.quadratic_endpoint_error V W e q x y G (G+one) H B
    hH hB (step_lower h B hB) hx hy

theorem actual_Barnes_finite_factorial_grid_increment_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
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
     let v := var 10
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h) ⋏ le ((e*stepDivisor R)*norm1 h) B) ⟶
       (previous M ≐ succ e ⋏ le e (previous J)) ⟶
       (le (observationClock z h R B r M e) t ⋏ le (quadraticClock B) u ⋏ le (quadraticClock B) v) ⟶
       distanceBounded
         (qmul (reciprocal (ofGaussian h B))
           (qsub (natScale two (ap2 F v (fd (add z h) (R+one) B r J e)))
             (natScale two (ap2 F u (fd z (R+one) B r J e))))) (mixedGrid t z h R B r e) (numerator R M e h) B) :=
  closeUniv 11 (.impI (.impI (.impI (rate _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₂
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalFiniteTaylorGridIncrementRate
