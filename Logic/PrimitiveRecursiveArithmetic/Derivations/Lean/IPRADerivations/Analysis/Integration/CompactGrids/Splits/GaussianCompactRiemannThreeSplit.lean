import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactNamedAdditivity

/-!
# Three actual compact quadratures at the same rational step

Two applications of the original finite split retain every original
evaluator call and its genuine zero-distance encoding error. The actual
piece counts are C1*K, C2*K, C3*K. No equality of differently encoded
observations is presumed. A local sampled modulus is the only evaluator
contract, and the explicit finite split error is retained.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactRiemannThreeSplit

open_ipra
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def input (F : PR 3) (a C1 C2 C3 E K L x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one C1 ⋏ (le one C2 ⋏ (le one C3 ⋏ (le one E ⋏ (le one K ⋏
    sampledModulus F a (C1+C2+C3) E L x)))))

theorem original_three_piece_split (F : PR 3) (s a C1 C2 C3 E K L x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 C3 E K L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s ((C1+C2+C3)*K) a (C1+C2+C3) E x)
      (qadd (qadd (quadrature F s (C1*K) a C1 E x)
        (quadrature F s (C2*K) (a+C1) C2 E x)) (quadrature F s (C3*K) (a+(C1+C2)) C3 E x))
      (two*(C1+C2+C3)+two*(C1+C2)) (E*unit s) := by
  have ha := h.andE₁
  have h1 := h.andE₂.andE₁
  have h2 := h.andE₂.andE₂.andE₁
  have h3 := h.andE₂.andE₂.andE₂.andE₁
  have he := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hk := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hm := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have h12 := GaussianCompactRiemannSplit.sum_width_positive C1 C2 h1
  have whole : Γ ⊢[PRAAx] GaussianCompactRiemannAdditivity.input F a (C1+C2) C3 E K L x :=
    .andI ha (.andI he (.andI hk (.andI h12 (.andI h3 hm))))
  have left : Γ ⊢[PRAAx] GaussianCompactRiemannAdditivity.input F a C1 C2 E K L x :=
    .andI ha (.andI he (.andI hk (.andI h1 (.andI h2
      (GaussianCompactNamedAdditivity.left_modulus F a (C1+C2) C3 E L x hm)))))
  have first := GaussianCompactRiemannAdditivity.shared_step_additivity F s a (C1+C2) C3 E K L x whole
  have second := GaussianCompactRiemannAdditivity.shared_step_additivity F s a C1 C2 E K L x left
  have hd := positive_product (Γ := Γ) E (unit s) he (unit_positive s)
  have lift := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd second
    (GaussianRationalPowerDifference.distance_refl_zero (quadrature F s (C3*K) (a+(C1+C2)) C3 E x) (E*unit s) hd)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd first lift)

theorem original_common_step_three_quadrature_split_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        distanceBounded
          (quadrature F (var 0) ((var 2+var 3+var 4)*var 6) (var 1) (var 2+var 3+var 4) (var 5) (var 8))
          (qadd (qadd (quadrature F (var 0) (var 2*var 6) (var 1) (var 2) (var 5) (var 8))
            (quadrature F (var 0) (var 3*var 6) (var 1+var 2) (var 3) (var 5) (var 8)))
              (quadrature F (var 0) (var 4*var 6) (var 1+(var 2+var 3)) (var 4) (var 5) (var 8)))
          (two*(var 2+var 3+var 4)+two*(var 2+var 3)) (var 5*unit (var 0))) :=
  closeUniv 9 (.impI (original_three_piece_split F _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactRiemannThreeSplit
