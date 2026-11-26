import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceGridEvenError
import IPRADerivations.Analysis.Polynomials.FiniteDifferences.GaussianPolynomialForwardDifferenceGridIncrement
import IPRADerivations.Analysis.Names.Rates.DifferenceQuotients.GaussianNamedDifferenceQuotient

/-!
# Exact increment of the sum of opposite normalized grids

A forward and a backward grid give two pairs of adjacent windows.
When the center advances by one step the forward offset increases and
the backward offset decreases. The signed parity changes by one power
of minus one, giving the combined grid of the next order exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridEvenIncrement

open_ipra
open GaussianNameArithmetic (sum_difference)
open GaussianNamedDifference (difference_distance)
open GaussianPolynomialForwardDifferenceGridEvenError (observedDouble)
open GaussianPolynomialForwardDifferenceGridIncrement (normalized_increment slice)
open GaussianPolynomialForwardDifferenceGridLinearity (normalized_combined)
open GaussianPolynomialForwardDifferenceNormalization (normalized)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalDistanceOrder (distance_radius_mono reversed_difference)
open GaussianRationalEulerCoefficients (parityPoint)
open GaussianRationalHorner (positive_product qadd qmul)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (distanceBounded qnegative qsub)
open GaussianRationalParityPower (parity_succ)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (bound_congr bounded_product reciprocal)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qsub_congr)
open GaussianReciprocalHorner (qmul_associative)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem swap_factors (s a x : PTm n) : Γ ⊢[PRAAx] qmul s (qmul a x) ≐ qmul a (qmul s x) :=
  (qmul_associative s a x).eqSymm.eqTrans
    ((qmul_congr (qmul_commutative s a) (.eqRefl x)).eqTrans (qmul_associative a s x))

private theorem backward_difference (e x y : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul (parityPoint e) x) (qmul (parityPoint e) y) ≐
      qmul (parityPoint (succ e)) (qsub y x) := by
  let a := parityPoint e
  let v := qsub y x
  have sign : Γ ⊢[PRAAx] qmul a (qnegative v) ≐ qmul (qnegative a) v :=
    (qmul_commutative a (qnegative v)).eqTrans
      ((GaussianInverseBinomialRows.negative_product v a).eqSymm.eqTrans
        ((GaussianInverseBinomialRows.negative_congr (qmul_commutative v a)).eqTrans
          (GaussianInverseBinomialRows.negative_product a v)))
  exact (multiplication_difference a x y).eqTrans
    ((qmul_congr (.eqRefl a) (reversed_difference y x).eqSymm).eqTrans
      (sign.eqTrans (qmul_congr (parity_succ e).eqSymm (.eqRefl v))))

/-- The quotient of the doubled order-e observations at two adjacent
centers is the doubled normalized order-(e+1) grid. The backward longer
window starts at the second center, so its offsets are reversed. -/
theorem increment (V W e h : PTm n) : Γ ⊢[PRAAx]
    qmul (reciprocal h)
      (qsub (observedDouble (slice V one (succ e)) (slice W zero (succ e)) e h)
        (observedDouble (slice V zero (succ e)) (slice W one (succ e)) e h)) ≐
      observedDouble V W (succ e) h := by
  let z := reciprocal h
  let f (j : PTm n) := normalized (slice V j (succ e)) e h
  let g (j : PTm n) := normalized (slice W j (succ e)) e h
  let p := parityPoint e
  let q := parityPoint (succ e)
  have left := normalized_combined (Γ := Γ) (slice V one (succ e)) (slice W zero (succ e)) qone p e h
  have right := normalized_combined (Γ := Γ) (slice V zero (succ e)) (slice W one (succ e)) qone p e h
  have split := (qsub_congr left right).eqTrans
    ((sum_difference (qmul qone (f one)) (qmul qone (f zero)) (qmul p (g zero)) (qmul p (g one))).eqTrans
      (qadd_congr (multiplication_difference qone (f one) (f zero)) (backward_difference e (g zero) (g one))))
  have advance_f := (swap_factors (Γ := Γ) z qone (qsub (f one) (f zero))).eqTrans
    (qmul_congr (.eqRefl qone) (normalized_increment V e h))
  have advance_g := (swap_factors (Γ := Γ) z q (qsub (g one) (g zero))).eqTrans
    (qmul_congr (.eqRefl q) (normalized_increment W e h))
  exact (qmul_congr (.eqRefl z) split).eqTrans
    ((qmul_add z _ _).eqTrans ((qadd_congr advance_f advance_g).eqTrans
      (normalized_combined V W qone q (succ e) h).eqSymm))

/-- Quadratic errors at the two adjacent centers become a linear error
after division by the step. The same step normalizes both grids. -/
theorem quadratic_endpoint_error (V W e h x y A C H B : PTm n)
    (hH : Γ ⊢[PRAAx] le one H) (hB : Γ ⊢[PRAAx] le one B)
    (hh : Γ ⊢[PRAAx] lower h H (two*B))
    (hx : Γ ⊢[PRAAx] distanceBounded x (observedDouble (slice V one (succ e)) (slice W zero (succ e)) e h)
      (A*(H*H)) (B*B))
    (hy : Γ ⊢[PRAAx] distanceBounded y (observedDouble (slice V zero (succ e)) (slice W one (succ e)) e h)
      (C*(H*H)) (B*B)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (reciprocal h) (qsub x y)) (observedDouble V W (succ e) h) (two*(A+C)*H) B := by
  let p := observedDouble (slice V one (succ e)) (slice W zero (succ e)) e h
  let q := observedDouble (slice V zero (succ e)) (slice W one (succ e)) e h
  let r := reciprocal h
  let xq := qmul r (qsub x y)
  let next := observedDouble V W (succ e) h
  have hB₂ := positive_product B B hB hB
  have hinv := GaussianRationalLowerBounds.inverse_bound h H (two*B) hH
    (positive_product two B (le_succ_self one) hB) hh
  have err := difference_distance x p y q (A*(H*H)) (C*(H*H)) (B*B) hB₂ hx hy
  have raw := bounded_product r (qsub (qsub x y) (qsub p q)) (two*B) H
    (A*(H*H)+C*(H*H)) (B*B) hH hB₂ hinv err
  have exact_diff : Γ ⊢[PRAAx] qsub xq next ≐ qmul r (qsub (qsub x y) (qsub p q)) :=
    (qsub_congr (.eqRefl xq) (increment V W e h).eqSymm).eqTrans
      (multiplication_difference r (qsub x y) (qsub p q))
  exact distance_radius_mono xq next ((two*B)*(A*(H*H)+C*(H*H))) (H*(B*B))
    (two*(A+C)*H) B (positive_product H (B*B) hH hB₂) hB
    (le_of_eq_add (d := zero) (by ipra_ring))
    (bound_congr exact_diff.eqSymm (.eqRefl _) (.eqRefl _) raw)

theorem actual_Gaussian_opposite_grid_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let V := var 0
     let W := var 1
     let e := var 2
     let h := var 3
     qmul (reciprocal h)
       (qsub (observedDouble (slice V one (succ e)) (slice W zero (succ e)) e h)
         (observedDouble (slice V zero (succ e)) (slice W one (succ e)) e h)) ≐
       observedDouble V W (succ e) h) :=
  closeUniv 4 (increment _ _ _ _)

theorem actual_Gaussian_opposite_grid_increment_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let V := var 0
     let W := var 1
     let e := var 2
     let h := var 3
     let x := var 4
     let y := var 5
     let A := var 6
     let C := var 7
     let H := var 8
     let B := var 9
     (le one H ⋏ le one B ⋏ lower h H (two*B)) ⟶
       (distanceBounded x (observedDouble (slice V one (succ e)) (slice W zero (succ e)) e h) (A*(H*H)) (B*B) ⋏
         distanceBounded y (observedDouble (slice V zero (succ e)) (slice W one (succ e)) e h) (C*(H*H)) (B*B)) ⟶
       distanceBounded (qmul (reciprocal h) (qsub x y)) (observedDouble V W (succ e) h) (two*(A+C)*H) B) :=
  closeUniv 10 (.impI (.impI (quadratic_endpoint_error _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceGridEvenIncrement
