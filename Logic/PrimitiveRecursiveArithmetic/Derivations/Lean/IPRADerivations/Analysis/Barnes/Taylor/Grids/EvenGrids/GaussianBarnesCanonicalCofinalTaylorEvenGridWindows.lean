import IPRADerivations.Analysis.Barnes.Taylor.Grids.EvenGrids.GaussianBarnesCanonicalCofinalTaylorEvenGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.Grids.Cofinal.GaussianBarnesCanonicalCofinalTaylorGridReturn

/-!
# Adjacent two-sided windows of the original cofinal Barnes grid

The two windows at the translated center have the original observation
codes. At the starting center only the backward return can change the
code. Its certified row error controls the parity-weighted observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorEvenGridWindows

open_ipra
open ComplexLogarithmRemainder (add bounded normSq)
open GaussianBarnesCanonicalCofinalTaylorEvenGridLimit (observed)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalGrid deadline)
open GaussianBarnesCanonicalCofinalTaylorGridReturn (return_window_rows)
open GaussianBarnesCanonicalCofinalTaylorGridWindows (first_window next_window)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (query_budget)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianPolynomialForwardDifferenceGridEvenError (even_error observedDouble)
open GaussianPolynomialForwardDifferenceGridIncrement (slice)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "gneg" => ComplexLogarithmRemainder.neg

private theorem observed_double_congr {V W P Q e h : PTm n}
    (hV : Γ ⊢[PRAAx] V ≐ P) (hW : Γ ⊢[PRAAx] W ≐ Q) :
    Γ ⊢[PRAAx] observedDouble V W e h ≐ observedDouble P Q e h := by
  ipra_congr (observedDouble (var 0) (var 1) (var 2) (var 3) : PTm 4)
    with [hV,hW,.eqRefl e,.eqRefl h]

private theorem reflexive_rows (V L D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] rowBound V V L zero D := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift L) :: Γ.map Fm.shift
  have pos : Δ ⊢[PRAAx] le one (Syn.shift D) := by simpa [Δ,Fm.shift,Syn.shift] using hD.shift.wk
  simpa [Δ,rowBound,Syn.shift] using
    GaussianRationalPowerDifference.distance_refl_zero (entry (Syn.shift V) (var 0)) (Syn.shift D) pos

theorem shifted_equal (t z h R B e : PTm n) :
    Γ ⊢[PRAAx] observedDouble
      (slice (cofinalGrid t z h R B (succ e)) one (succ e))
      (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) zero (succ e)) e (ofGaussian h B) ≐
      observed t (add z h) h R B e :=
  observed_double_congr (next_window t z h R B e) (first_window t (add z h) (gneg h) R B e)

theorem centered_rate (p t z h R B H e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (ht : Γ ⊢[PRAAx] le (deadline p B e) t) :
    Γ ⊢[PRAAx] distanceBounded (observed t z h R B e)
      (observedDouble (slice (cofinalGrid t z h R B (succ e)) zero (succ e))
        (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e)) e (ofGaussian h B)) one (unit p) := by
  let V := slice (cofinalGrid t z h R B (succ e)) zero (succ e)
  let W := slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e)
  let U := cofinalGrid t z (gneg h) R B e
  let T := unit t*unit t
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ (unit_positive t) (unit_positive t)
  have raw := even_error V W V U e (ofGaussian h B) one B zero (unit t+unit t) T
    (le_refl one) hz.andE₁ (GaussianNamedDifferenceQuotient.parameter_lower h B (.andI hz.andE₁ hn)) hT
    (reflexive_rows V (succ e) T hT) (return_window_rows t t z h R B H e hz hh hs)
  have actual : Γ ⊢[PRAAx] observedDouble V U e (ofGaussian h B) ≐ observed t z h R B e :=
    observed_double_congr (first_window t z h R B e) (.eqRefl U)
  have near : Γ ⊢[PRAAx] distanceBounded (observedDouble V W e (ofGaussian h B)) (observed t z h R B e)
      (pw B e*(pw two e*(unit t+unit t))) T :=
    distance_congr (.eqRefl _) actual (by ipra_ring)
      ((congrMul (GaussianPolynomialPerturbation.one_power e) (.eqRefl T)).eqTrans (one_mul T)) raw
  have enough : Γ ⊢[PRAAx] le (num 3*(pw B e*pw two e)*unit p) (unit t) :=
    le_trans (query_budget _ _) (GaussianExponentialReference.unit_monotone ht)
  have twice : Γ ⊢[PRAAx] le (two*(pw B e*pw two e)*unit p) (unit t) :=
    le_trans (le_of_eq_add (d := (pw B e*pw two e)*unit p) (by ipra_ring)) enough
  have comparison : Γ ⊢[PRAAx] le ((pw B e*(pw two e*(unit t+unit t)))*unit p) (one*T) :=
    le_congr (by ipra_ring) (one_mul _).eqSymm (mul_le_mul_right (unit t) twice)
  exact distance_symmetric _ _ _ _ (unit_positive p)
    (distance_radius_mono _ _ _ _ _ _ hT (unit_positive p) comparison near)

theorem actual_Barnes_cofinal_even_windows_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let p := var 0
       let t := var 1
       let z := var 2
       let h := var 3
       let R := var 4
       let B := var 5
       let H := var 6
       let e := var 7
       let V := cofinalGrid t z h R B (succ e)
       let W := cofinalGrid t (add z h) (gneg h) R B (succ e)
       let q := ofGaussian h B
       (observedDouble (slice V one (succ e)) (slice W zero (succ e)) e q ≐ observed t (add z h) h R B e) ⋏
         ((source z R B ⋏ (bounded h H ⋏ (le (e*H) B ⋏ (le one (normSq h) ⋏ le (deadline p B e) t)))) ⟶
           distanceBounded (observed t z h R B e)
             (observedDouble (slice V zero (succ e)) (slice W one (succ e)) e q) one (unit p))) :=
  closeUniv 8 (.andI (shifted_equal _ _ _ _ _ _) (.impI (centered_rate _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorEvenGridWindows
