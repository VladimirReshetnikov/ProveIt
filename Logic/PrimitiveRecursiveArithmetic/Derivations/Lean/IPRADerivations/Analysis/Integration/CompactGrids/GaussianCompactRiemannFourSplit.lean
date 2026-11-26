import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactZeroSafeSplit

/-!
# Four actual compact quadratures at a common rational step

All four widths may be zero. The actual piece counts are their widths
times the common numerical mesh factor. A balanced pair of the checked
zero-safe two-piece splits retains the original evaluator and its real
encoding errors, with total error 4*(sum widths)/(E*2^s).
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCompactRiemannFourSplit

open_ipra
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCompactRiemannName (quadrature sampledModulus)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def totalWidth (C1 C2 C3 C4 : PTm n) : PTm n := (C1+C2)+(C3+C4)
def pieces (F : PR 3) (s a C1 C2 C3 C4 E K x : PTm n) : PTm n :=
  qadd (qadd (quadrature F s (C1*K) a C1 E x) (quadrature F s (C2*K) (a+C1) C2 E x))
    (qadd (quadrature F s (C3*K) (a+(C1+C2)) C3 E x) (quadrature F s (C4*K) ((a+(C1+C2))+C3) C4 E x))
def input (F : PR 3) (a C1 C2 C3 C4 E K L x : PTm n) : Fm PTm n :=
  le one a ⋏ (le one E ⋏ (le one K ⋏ sampledModulus F a (totalWidth C1 C2 C3 C4) E L x))
ipra_subst totalWidth
ipra_subst pieces
ipra_subst input

/-- The original shared-step split, with every zero-width case included. -/
theorem original_four_piece_split (F : PR 3) (s a C1 C2 C3 C4 E K L x : PTm n)
    (h : Γ ⊢[PRAAx] input F a C1 C2 C3 C4 E K L x) : Γ ⊢[PRAAx]
    distanceBounded (quadrature F s (totalWidth C1 C2 C3 C4*K) a (totalWidth C1 C2 C3 C4) E x)
      (pieces F s a C1 C2 C3 C4 E K x) (num 4*totalWidth C1 C2 C3 C4) (E*unit s) := by
  have ha := h.andE₁
  have he := h.andE₂.andE₁
  have hk := h.andE₂.andE₂.andE₁
  have hm := h.andE₂.andE₂.andE₂
  have leftMod := GaussianCompactNamedAdditivity.left_modulus F a (C1+C2) (C3+C4) E L x hm
  have rightMod := GaussianCompactNamedAdditivity.right_modulus F a (C1+C2) (C3+C4) E L x hm
  have first := GaussianCompactZeroSafeSplit.shared_step_additivity F s a (C1+C2) (C3+C4) E K L x
    (.andI ha (.andI he (.andI hk hm)))
  have second := GaussianCompactZeroSafeSplit.shared_step_additivity F s a C1 C2 E K L x
    (.andI ha (.andI he (.andI hk leftMod)))
  have third := GaussianCompactZeroSafeSplit.shared_step_additivity F s (a+(C1+C2)) C3 C4 E K L x
    (.andI (le_trans ha (le_add_right _ _)) (.andI he (.andI hk rightMod)))
  have hd := positive_product (Γ := Γ) E (unit s) he (unit_positive s)
  have both := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd second third
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold totalWidth; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd first both)

theorem original_zero_safe_common_step_four_split_closed (F : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (input F (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
        distanceBounded
          (quadrature F (var 0) (totalWidth (var 2) (var 3) (var 4) (var 5)*var 7) (var 1)
            (totalWidth (var 2) (var 3) (var 4) (var 5)) (var 6) (var 9))
          (pieces F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 9))
          (num 4*totalWidth (var 2) (var 3) (var 4) (var 5)) (var 6*unit (var 0))) :=
  closeUniv 10 (.impI (original_four_piece_split F _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianCompactRiemannFourSplit
