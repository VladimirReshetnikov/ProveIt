import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalCofinalTaylorEvenGridWindows
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.Grids.GaussianPolynomialForwardDifferenceGridEvenIncrement

/-!
# Actual Barnes factorial quotient and the next difference grid

The two endpoints use independently observed cofinal order-e factorial
names. The neighboring opposite grids approximate them quadratically.
The quotient consequently has a linear bound against the doubled
order-(e+1) grid made from the two longer, oppositely directed windows.
-/

set_option autoImplicit false
set_option maxHeartbeats 1150000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridIncrementRate

open_ipra
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalCofinalTaylorEvenGridLimit (observationClock observed uniformGain uniform_rate)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalGrid)
open GaussianBarnesCanonicalFiniteTaylorEvenGridLimit (quadraticClock)
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

local notation "F" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "gneg" => ComplexLogarithmRemainder.neg
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def mixedGrid (t z h R B e : PTm n) : PTm n :=
  observedDouble (cofinalGrid t z h R B (succ e))
    (cofinalGrid t (add z h) (gneg h) R B (succ e)) (succ e) (ofGaussian h B)

def numerator (R M e h : PTm n) : PTm n := two*(uniformGain R M e+(uniformGain R M e+one))*norm1 h

private theorem step_lower (h B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ofGaussian h B) (norm1 h) (two*B) := by
  apply lower_from_representation _ h B _ _ hB (positive_product _ _ (le_succ_self one) hB)
    (ofGaussian_represents h B hB)
  have hs := norm1_square_le_two_normSq (Γ := Γ) h
  ipra_le 𝔞(B)*𝔞(B)*(sl hs+2*𝔞(normSq h))

theorem rate (z h R B M J e t u v : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hw : Γ ⊢[PRAAx] source (add z h) R B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hsmall : Γ ⊢[PRAAx] le ((e*stepDivisor R)*norm1 h) B)
    (hdeg : Γ ⊢[PRAAx] previous M ≐ succ e) (hJ : Γ ⊢[PRAAx] le e (previous J))
    (ht : Γ ⊢[PRAAx] le (observationClock B e) t)
    (hu : Γ ⊢[PRAAx] le (quadraticClock B) u) (hv : Γ ⊢[PRAAx] le (quadraticClock B) v) : Γ ⊢[PRAAx]
    distanceBounded
      (qmul (reciprocal (ofGaussian h B))
        (qsub (natScale two (ap2 F v (fd (add z h) (R+one) B J e)))
          (natScale two (ap2 F u (fd z (R+one) B J e))))) (mixedGrid t z h R B e) (numerator R M e h) B := by
  let V := cofinalGrid t z h R B (succ e)
  let W := cofinalGrid t (add z h) (gneg h) R B (succ e)
  let H := norm1 h
  let Q := B*B
  let k := quadraticClock B
  let G := uniformGain R M e
  let q := ofGaussian h B
  let x := natScale two (ap2 F v (fd (add z h) (R+one) B J e))
  let y := natScale two (ap2 F u (fd z (R+one) B J e))
  let A := observedDouble (slice V one (succ e)) (slice W zero (succ e)) e q
  let C := observedDouble (slice V zero (succ e)) (slice W one (succ e)) e q
  let O := observed t z h R B e
  have hB := hz.andE₁
  have hQ := positive_product B B hB hB
  have hH := GaussianNativeDerivativeQuotientRate.norm1_positive h hn
  have hH₂ := positive_product H H hH hH
  have width : Γ ⊢[PRAAx] le (e*H) B := by
    have one_le := stepDivisor_positive (Γ := Γ) R
    have mono := mul_le_mul_right H (mul_le_mul_right e one_le)
    exact le_trans (le_congr (by ipra_ring) (by ipra_ring) mono) hsmall
  have left := uniform_rate (add z h) h R B M J e t v hw hn hsmall hdeg hJ ht hv
  have right := uniform_rate z h R B M J e t u hz hn hsmall hdeg hJ ht hu
  have hx : Γ ⊢[PRAAx] distanceBounded x A (G*(H*H)) Q :=
    distance_congr (.eqRefl _) (GaussianBarnesCanonicalCofinalTaylorEvenGridWindows.shifted_equal t z h R B e).eqSymm
      (.eqRefl _) (.eqRefl _) (distance_symmetric _ _ _ _ hQ left)
  have center := GaussianBarnesCanonicalCofinalTaylorEvenGridWindows.centered_rate k t z h R B H e hz
    (normSq_le_norm1_square h) width hn ht
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

theorem actual_Barnes_cofinal_factorial_grid_increment_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let M := var 4
     let J := var 5
     let e := var 6
     let t := var 7
     let u := var 8
     let v := var 9
     (source z R B ⋏ source (add z h) R B ⋏ le one (normSq h) ⋏ le ((e*stepDivisor R)*norm1 h) B) ⟶
       (previous M ≐ succ e ⋏ le e (previous J)) ⟶
       (le (observationClock B e) t ⋏ le (quadraticClock B) u ⋏ le (quadraticClock B) v) ⟶
       distanceBounded
         (qmul (reciprocal (ofGaussian h B))
           (qsub (natScale two (ap2 F v (fd (add z h) (R+one) B J e)))
             (natScale two (ap2 F u (fd z (R+one) B J e))))) (mixedGrid t z h R B e) (numerator R M e h) B) :=
  closeUniv 10 (.impI (.impI (.impI (rate _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.wk.andE₁ Prf.hyp1.wk.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₁ Prf.hyp1.wk.andE₂.andE₂.andE₂
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridIncrementRate
