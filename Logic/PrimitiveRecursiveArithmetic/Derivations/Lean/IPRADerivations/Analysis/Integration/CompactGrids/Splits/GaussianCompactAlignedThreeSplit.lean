import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactAlignedSplit

/-!
# Three actual shared-step compact grids from aligned samples

The third interval stays contiguous. Two genuine zero-safe aligned-time
splits retain every original evaluator call and yield a split allowance
at most 4 times the total width over E*2^s. All widths may be zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactAlignedThreeSplit

open_ipra
open GaussianCompactAlignedTime (alignedSamples)
open GaussianCompactRiemannName (quadrature)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def pieces (F : PR 3) (s a C1 C2 C3 E K x : PTm n) : PTm n :=
  qadd (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x))
    (quadrature F s (C3*K) (a+(C1+C2)) C3 E x)
def input (F : PR 3) (a C1 C2 C3 E K x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ alignedSamples F a (C1+C2+C3) E x))

theorem original_three_piece_split (F : PR 3) (s a C1 C2 C3 E K x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 C3 E K x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s ((C1+C2+C3)*K) a (C1+C2+C3) E x)
      (pieces F s a C1 C2 C3 E K x) (num 4*(C1+C2+C3)) (E*unit s) := by
  have first := GaussianCompactAlignedSplit.shared_step_additivity F s a (C1+C2) C3 E K x h
  have second := GaussianCompactAlignedSplit.shared_step_additivity F s a C1 C2 E K x
    (.andI h.andE₁ (.andI h.andE₂.andE₁ (.andI h.andE₂.andE₂.andE₁
      (GaussianCompactAlignedTime.left_aligned F a (C1+C2) C3 E x h.andE₂.andE₂.andE₂))))
  have hd := positive_product (Γ := Γ) E (unit s) h.andE₂.andE₁ (unit_positive s)
  have lift := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd second
    (GaussianRationalPowerDifference.distance_refl_zero (quadrature F s (C3*K) (a+(C1+C2)) C3 E x) (E*unit s) hd)
  have joined := distance_triangle_same _ _ _ _ _ _ hd first lift
  apply distance_radius_mono _ _ _ _ _ _ hd hd _ joined
  exact le_of_eq_add (d := two*C3*(E*unit s)) (by ipra_ring)

theorem actual_aligned_time_three_contiguous_grids_closed (F : PR 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (quadrature F (var 0) ((var 2+var 3+var 4)*var 6) (var 1) (var 2+var 3+var 4) (var 5) (var 7))
        (pieces F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (num 4*(var 2+var 3+var 4)) (var 5*unit (var 0))) :=
  closeUniv 8 (.impI (original_three_piece_split F _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactAlignedThreeSplit
