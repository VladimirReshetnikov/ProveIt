import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerBlockWeight

/-!
# The actual lower-panel sum with a retained numerical coefficient

The existing two width inequalities are used unchanged. A coefficient C
multiplying each actual row radius multiplies only the final finite block
radius. The original finite sum and actual weight remain literal. This
allows the factorial coefficient in the logarithmic lower-tail estimate
to pass through the existing root partition without changing its program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianScaledLowerBlockWeight

open_ipra
open GaussianEulerLowerBlockWeight (source rowNumerator rowDenominator numerator denominator row_denominator_positive width_numerator)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalFiniteSum (sum)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem actual_block_bound (w x C N D u v S L P : PTm n)
    (h : Γ ⊢[PRAAx] source N D u v S P)
    (hw : Γ ⊢[PRAAx] bounded w one (D*u))
    (hx : Γ ⊢[PRAAx] bounded x (N*(C*rowNumerator D u v S L P)) (rowDenominator D v P)) :
    Γ ⊢[PRAAx] bounded (qmul w x) (C*numerator D S L P) (denominator D P) := by
  have hD := h.andE₁
  have hu := h.andE₂.andE₁
  have hv := h.andE₂.andE₂.andE₁
  have hp := h.andE₂.andE₂.andE₂.andE₁
  have hRow := row_denominator_positive D v P hD hv hp
  have hWeight := positive_product _ _ hD hu
  have actual := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hWeight hRow hw hx
  have width := mul_le_mul_right C (width_numerator N D u v S L P
    h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hWeight hRow) (positive_product _ _ (positive_product _ _ hD hD) hp)
    (le_congr (by unfold denominator; ipra_ring) (by unfold denominator rowDenominator; ipra_ring)
      (mul_le_mul_right (denominator D P) width)) actual

theorem actual_finite_block_bound (f : PTm 2) (w x C N D u v S L P : PTm n)
    (h : Γ ⊢[PRAAx] source N D u v S P)
    (hw : Γ ⊢[PRAAx] bounded w one (D*u))
    (hRows : Γ ⊢[PRAAx] summandsBounded f N x (C*rowNumerator D u v S L P) (rowDenominator D v P)) :
    Γ ⊢[PRAAx] bounded (qmul w (sum f N x)) (C*numerator D S L P) (denominator D P) :=
  actual_block_bound w _ C N D u v S L P h hw
    (uniform_sum_bound f N x _ _
      (row_denominator_positive D v P h.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁) hRows)

theorem actual_scaled_lower_block_weight_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 3) (var 4) (var 5) (var 6) (var 7) (var 9) ⟶
      bounded (var 0) one (var 4*var 5) ⟶
      summandsBounded f (var 3) (var 1)
        (var 2*rowNumerator (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) (rowDenominator (var 4) (var 6) (var 9)) ⟶
      bounded (qmul (var 0) (sum f (var 3) (var 1)))
        (var 2*numerator (var 4) (var 7) (var 8) (var 9)) (denominator (var 4) (var 9))) :=
  closeUniv 10 (.impI (.impI (.impI (actual_finite_block_bound f _ _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianScaledLowerBlockWeight
