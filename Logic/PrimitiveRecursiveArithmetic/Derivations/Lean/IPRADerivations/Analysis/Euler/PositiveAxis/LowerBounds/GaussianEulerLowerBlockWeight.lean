import IPRADerivations.Analysis.FiniteOperations.GaussianUniformFiniteSumBound

/-!
# Uniform weighted radius of an actual lower-tail block

The singular row term u/v uses the genuine width bound n<=S*v.
The Lipschitz and observation terms use the distinct n<=S*u.
The original uniform finite-sum bound and bounded_product for the
actual weight 1/(D*u) then give the exact uniform block radius.
No desired weighted bound or denominator cancellation is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerBlockWeight

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalFiniteSum (sum)
open GaussianUniformFiniteSumBound (summandsBounded uniform_sum_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowNumerator (D u v S L P : PTm n) : PTm n := u*D*P+L*S*v*P+num 3*v*D
def rowDenominator (D v P : PTm n) : PTm n := v*D*P
def numerator (D S L P : PTm n) : PTm n := S*(D*P+L*S*P+num 3*D)
def denominator (D P : PTm n) : PTm n := D*D*P
def source (N D u v S P : PTm n) : Fm PTm n := le one D ⋏ (le one u ⋏ (le one v ⋏ (le one P ⋏ (le N (S*v) ⋏ le N (S*u)))))
ipra_subst rowNumerator
ipra_subst rowDenominator
ipra_subst numerator
ipra_subst denominator
ipra_subst source

theorem row_denominator_positive (D v P : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hv : Γ ⊢[PRAAx] le one v) (hP : Γ ⊢[PRAAx] le one P) : Γ ⊢[PRAAx]
    le one (rowDenominator D v P) := positive_product _ _ (positive_product _ _ hv hD) hP

theorem width_numerator (N D u v S L P : PTm n) (hv : Γ ⊢[PRAAx] le N (S*v)) (hu : Γ ⊢[PRAAx] le N (S*u)) : Γ ⊢[PRAAx]
    le (N*rowNumerator D u v S L P) (numerator D S L P*u*v) :=
  le_congr (by unfold rowNumerator; ipra_ring) (by unfold numerator; ipra_ring)
    (add_le_add₂ (mul_le_mul_right (u*D*P) hv) (mul_le_mul_right (L*S*v*P+num 3*v*D) hu))

/-- Pure actual-point conversion. The block sum has its derived uniform
row radius; the weight has the original 1/(D*u) radius. -/
theorem block_bound (w x N D u v S L P : PTm n) (h : Γ ⊢[PRAAx] source N D u v S P)
    (hw : Γ ⊢[PRAAx] bounded w one (D*u))
    (hx : Γ ⊢[PRAAx] bounded x (N*rowNumerator D u v S L P) (rowDenominator D v P)) : Γ ⊢[PRAAx]
    bounded (qmul w x) (numerator D S L P) (denominator D P) := by
  have hD := h.andE₁
  have hu := h.andE₂.andE₁
  have hv := h.andE₂.andE₂.andE₁
  have hP := h.andE₂.andE₂.andE₂.andE₁
  have hRow := row_denominator_positive D v P hD hv hP
  have hWeight := positive_product _ _ hD hu
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hWeight hRow hw hx
  have clear := mul_le_mul_right (denominator D P) (width_numerator N D u v S L P h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hWeight hRow)
    (positive_product _ _ (positive_product _ _ hD hD) hP)
    (le_congr (by unfold denominator; ipra_ring) (by unfold denominator rowDenominator; ipra_ring) clear) raw

/-- The unchanged original finite sum discharges the block-sum premise
from actual per-row bounds. No new sum recursor is introduced. -/
theorem finite_block_bound (f : PTm 2) (w x N D u v S L P : PTm n) (h : Γ ⊢[PRAAx] source N D u v S P)
    (hw : Γ ⊢[PRAAx] bounded w one (D*u))
    (hRows : Γ ⊢[PRAAx] summandsBounded f N x (rowNumerator D u v S L P) (rowDenominator D v P)) : Γ ⊢[PRAAx]
    bounded (qmul w (sum f N x)) (numerator D S L P) (denominator D P) :=
  block_bound w _ N D u v S L P h hw (uniform_sum_bound f N x _ _
    (row_denominator_positive D v P h.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁) hRows)

theorem exact_lower_block_width_conversion_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le (var 0) (var 4*var 3) ⋏ le (var 0) (var 4*var 2)) ⟶
      le (var 0*rowNumerator (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) (numerator (var 1) (var 4) (var 5) (var 6)*var 2*var 3)) :=
  closeUniv 7 (.impI (width_numerator _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_uniform_lower_block_sum_weight_closed (f : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 8) ⟶ bounded (var 0) one (var 3*var 4) ⟶
      summandsBounded f (var 2) (var 1) (rowNumerator (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)) (rowDenominator (var 3) (var 5) (var 8)) ⟶
      bounded (qmul (var 0) (sum f (var 2) (var 1))) (numerator (var 3) (var 6) (var 7) (var 8)) (denominator (var 3) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (finite_block_bound f _ _ _ _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerLowerBlockWeight
