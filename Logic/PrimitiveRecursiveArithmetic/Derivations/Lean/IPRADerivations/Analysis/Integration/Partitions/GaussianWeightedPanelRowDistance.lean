import IPRADerivations.Analysis.Names.GaussianNameArithmetic

/-!
# One actual weighted panel row with independently observed kernels

A weight of norm at most 1/H pays exactly one H-th of each original
point observation error. The independent width error contributes only
its true kernel majorant. No common value denominator is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianWeightedPanelRowDistance

open_ipra
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_product bounded_sum bound_congr)
open GaussianRationalDistanceOrder (distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (L K A M U V : PTm n) : PTm n := (L+two*K)*A*U*V+M*(U+V)
def denominator (H M U V : PTm n) : PTm n := H*(M*U*V)

ipra_subst numerator
ipra_subst denominator

theorem original_row_distance (x y u v L K A M H U V : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hH : Γ ⊢[PRAAx] le one H)
    (hU : Γ ⊢[PRAAx] le one U) (hV : Γ ⊢[PRAAx] le one V)
    (hxy : Γ ⊢[PRAAx] distanceBounded x y (L*A*U*V+M*(U+V)) (M*U*V))
    (hu : Γ ⊢[PRAAx] bounded u one H) (hy : Γ ⊢[PRAAx] bounded y K one)
    (huv : Γ ⊢[PRAAx] distanceBounded u v (two*A) (M*H)) : Γ ⊢[PRAAx]
    distanceBounded (qmul x u) (qmul y v) (numerator L K A M U V) (denominator H M U V) := by
  let P := L*A*U*V+M*(U+V)
  let Q := M*U*V
  have hQ : Γ ⊢[PRAAx] le one Q := positive_product _ _ (positive_product _ _ hM hU) hV
  have hMH := positive_product _ _ hM hH
  have first := bounded_product (qsub x y) u P Q one H hQ hH hxy hu
  have last := bounded_product y (qsub u v) K one (two*A) (M*H) (le_refl one) hMH hy huv
  have hd₁ := positive_product _ _ hQ hH
  have hd₂ := positive_product _ _ (le_refl one) hMH
  have raw := bound_congr (GaussianRationalPowerDifference.product_difference x y u v).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_sum _ _ _ _ _ _ hd₁ hd₂ first last)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd₁ hd₂)
    (positive_product _ _ hH hQ) (le_of_eq_add (d := zero) (by dsimp only [P,Q,numerator,denominator]; ipra_ring)) raw


theorem actual_original_weighted_panel_row_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (((le one (var 7) ⋏ (le one (var 8) ⋏ (le one (var 9) ⋏ le one (var 10)))) ⋏
      (distanceBounded (var 0) (var 1) (var 4*var 6*var 9*var 10+var 7*(var 9+var 10)) (var 7*var 9*var 10) ⋏
        (bounded (var 2) one (var 8) ⋏ (bounded (var 1) (var 5) one ⋏
          distanceBounded (var 2) (var 3) (two*var 6) (var 7*var 8))))) ⟶
      distanceBounded (qmul (var 0) (var 2)) (qmul (var 1) (var 3))
        (numerator (var 4) (var 5) (var 6) (var 7) (var 9) (var 10)) (denominator (var 8) (var 7) (var 9) (var 10))) :=
  closeUniv 11 (.impI (original_row_distance _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂.andE₁ Prf.hyp0.andE₁.andE₂.andE₂.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianWeightedPanelRowDistance
