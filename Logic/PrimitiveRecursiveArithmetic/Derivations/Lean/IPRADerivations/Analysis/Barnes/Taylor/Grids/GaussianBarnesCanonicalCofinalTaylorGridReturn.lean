import IPRADerivations.Analysis.Barnes.Taylor.Grids.GaussianBarnesCanonicalCofinalTaylorGridWindows
import IPRADerivations.Analysis.Barnes.CanonicalProducts.GaussianBarnesCanonicalProperness

/-!
# Backward windows of the original cofinal Barnes grid

Translation by a step and its negative returns to the same decoded
Gaussian point. Chart properness controls the two actual observation
codes and their normalized forward differences at independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridReturn

open_ipra
open ComplexLogarithmRemainder (add bounded normSq scale)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinal_at cofinalGrid deadline node_source)
open GaussianBarnesCanonicalCofinalTaylorGridWindows (next_window)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (query_budget)
open GaussianPolynomialForwardDifferenceGridError (rowBound)
open GaussianPolynomialForwardDifferenceGridIncrement (slice)
open GaussianPolynomialForwardDifferenceNormalization (normalized normalized_error)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product represents_congr)
open GaussianRationalMetric (distanceBounded)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_neg im_neg normSq_equal)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "gneg" => ComplexLogarithmRemainder.neg

private def returnCenter (z h : PTm n) : PTm n := add (add z h) (gneg h)

private theorem return_node_equal (z h j : PTm n) :
    Γ ⊢[PRAAx] equal (add (returnCenter z h) (scale j (gneg h))) (add z (scale j (gneg h))) := by
  apply equal_of_values <;> simp only [returnCenter,re_add,im_add,re_neg,im_neg] <;> ring

theorem return_point_fraction_equal (z h B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] ofGaussian (add (add (add z h) (gneg h)) (scale j (gneg h))) B ≐
      ofGaussian (add z (scale j (gneg h))) B :=
  canonical_unique _ _ _ _ (ofGaussian_canonical _ _ hB) (ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) (return_node_equal z h j) (.eqRefl _) (ofGaussian_represents _ _ hB))
    (ofGaussian_represents _ _ hB)

theorem return_window_at (t u z h R B H e j : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B)
    (hj : Γ ⊢[PRAAx] lt j (succ e)) :
    Γ ⊢[PRAAx] distanceBounded
      (entry (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e)) j)
      (entry (cofinalGrid u z (gneg h) R B e) j)
      (unit t+unit u) (unit t*unit u) := by
  let a := add (returnCenter z h) (scale j (gneg h))
  let b := add z (scale j (gneg h))
  have step : Γ ⊢[PRAAx] bounded (gneg h) H :=
    le_congr (ComplexLogarithmRemainder.normSq_neg h).eqSymm (.eqRefl _) hh
  have range : Γ ⊢[PRAAx] le j e := (succ_monus_succ _ _).eqSymm.eqTrans hj
  have sb : Γ ⊢[PRAAx] source b (R+one) B := node_source z (gneg h) R B H e j hz step hs range
  have sa : Γ ⊢[PRAAx] source a (R+one) B :=
    .andI sb.andE₁ (le_congr (normSq_equal (return_node_equal z h j)).eqSymm (.eqRefl _) sb.andE₂)
  have near := GaussianBarnesCanonicalProperness.comparison_at a b (R+one) (R+one) B B t u
    sa sb (return_point_fraction_equal z h B j hz.andE₁)
  have fromWindow := (entry_congr (next_window (Γ := Γ) t (add z h) (gneg h) R B e) (.eqRefl j)).eqTrans
    (cofinal_at t (returnCenter z h) (gneg h) R B e j hj)
  exact distance_congr fromWindow.eqSymm (cofinal_at u z (gneg h) R B e j hj).eqSymm (.eqRefl _) (.eqRefl _) near

theorem return_window_rows (t u z h R B H e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) :
    Γ ⊢[PRAAx] rowBound (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e))
      (cofinalGrid u z (gneg h) R B e) (succ e) (unit t+unit u) (unit t*unit u) := by
  refine .allI (.impI ?_)
  let s (a : PTm n) := Syn.shift a
  let j : PTm (n+1) := var 0
  let Δ := lt j (succ (s e)) :: Γ.map Fm.shift
  have hz' : Δ ⊢[PRAAx] source (s z) (s R) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
  have hh' : Δ ⊢[PRAAx] bounded (s h) (s H) := by simpa [Δ,s,Fm.shift,Syn.shift] using hh.shift.wk
  have hs' : Δ ⊢[PRAAx] le (s e*s H) (s B) := by simpa [Δ,s,Fm.shift,Syn.shift] using hs.shift.wk
  simpa [rowBound,Δ,s,j,Syn.shift,one] using
    return_window_at (s t) (s u) (s z) (s h) (s R) (s B) (s H) (s e) j hz' hh' hs' (Prf.hyp0 : Δ ⊢[PRAAx] _)

theorem return_window_normalized (t u z h R B H e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hn : Γ ⊢[PRAAx] le one (normSq h)) :
    Γ ⊢[PRAAx] distanceBounded
      (normalized (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e)) e (ofGaussian (gneg h) B))
      (normalized (cofinalGrid u z (gneg h) R B e) e (ofGaussian (gneg h) B))
      (pw B e*(pw two e*(unit t+unit u))) (unit t*unit u) :=
  normalized_error _ _ e (ofGaussian (gneg h) B) B _ _ hz.andE₁
    (GaussianNamedDifferenceQuotient.parameter_lower (gneg h) B
      (.andI hz.andE₁ (le_congr (.eqRefl _) (ComplexLogarithmRemainder.normSq_neg h).eqSymm hn)))
    (positive_product _ _ (unit_positive t) (unit_positive u)) (return_window_rows t u z h R B H e hz hh hs)

theorem return_window_scheduled (p t z h R B H e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hh : Γ ⊢[PRAAx] bounded h H) (hs : Γ ⊢[PRAAx] le (e*H) B) (hn : Γ ⊢[PRAAx] le one (normSq h))
    (ht : Γ ⊢[PRAAx] le (deadline p B e) t) :
    Γ ⊢[PRAAx] distanceBounded
      (normalized (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e)) e (ofGaussian (gneg h) B))
      (normalized (cofinalGrid t z (gneg h) R B e) e (ofGaussian (gneg h) B)) one (unit p) := by
  have enough : Γ ⊢[PRAAx] le (num 3*(pw B e*pw two e)*unit p) (unit t) :=
    le_trans (query_budget _ _) (GaussianExponentialReference.unit_monotone ht)
  have twice : Γ ⊢[PRAAx] le (two*(pw B e*pw two e)*unit p) (unit t) :=
    le_trans (le_of_eq_add (d := (pw B e*pw two e)*unit p) (by ipra_ring)) enough
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive t))
    (unit_positive p) (le_congr (by ipra_ring) (one_mul _).eqSymm (mul_le_mul_right (unit t) twice))
    (return_window_normalized t t z h R B H e hz hh hs hn)

theorem actual_Barnes_cofinal_grid_return_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let t := var 0
     let u := var 1
     let z := var 2
     let h := var 3
     let R := var 4
     let B := var 5
     let H := var 6
     let e := var 7
     (source z R B ⋏ (bounded h H ⋏ (le (e*H) B ⋏ le one (normSq h)))) ⟶
       distanceBounded
         (normalized (slice (cofinalGrid t (add z h) (gneg h) R B (succ e)) one (succ e)) e (ofGaussian (gneg h) B))
         (normalized (cofinalGrid u z (gneg h) R B e) e (ofGaussian (gneg h) B))
         (pw B e*(pw two e*(unit t+unit u))) (unit t*unit u)) :=
  closeUniv 8 (.impI (return_window_normalized _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridReturn
