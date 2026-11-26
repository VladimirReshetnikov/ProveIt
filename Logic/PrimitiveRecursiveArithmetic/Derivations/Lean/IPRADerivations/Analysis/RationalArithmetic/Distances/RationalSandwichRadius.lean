import IPRADerivations.Analysis.RationalArithmetic.RationalValueBounds
import IPRADerivations.Analysis.Optimization.RationalArgmin

/-!
# Exact scalar radius bounds inside an ordered sandwich

Two endpoint radii to an arbitrary raw anchor bound every actual scalar
between the endpoints. Independent endpoint perturbations add exactly
their original rational radius to the reference interval width.
No common decoded denominator, canonicality or sign premise is needed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalSandwichRadius

open_ipra
open RationalArgmin (rationalLE)
open RationalValueBounds (radius upper_of_radius radius_symmetric radius_of_upper upper_order_left upper_order_right radius_triangle radius_congr radius_diagonal)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The anchor may lie anywhere relative to the interval. -/
theorem sandwich_radius (u x v y A B : PTm n)
    (hux : Γ ⊢[PRAAx] rationalLE u x) (hxv : Γ ⊢[PRAAx] rationalLE x v)
    (hu : Γ ⊢[PRAAx] radius u y A B) (hv : Γ ⊢[PRAAx] radius v y A B) : Γ ⊢[PRAAx]
    radius x y A B :=
  radius_of_upper x y A B
    (upper_order_left x v y A B hxv (upper_of_radius v y A B hv))
    (upper_order_right y u x A B (upper_of_radius y u A B (radius_symmetric u y A B hu)) hux)

/-- A scalar between perturbed endpoints stays within the reference
width plus exactly one endpoint perturbation of the right anchor. -/
theorem perturbed_endpoints (u x v s r A B C D : PTm n)
    (hux : Γ ⊢[PRAAx] rationalLE u x) (hxv : Γ ⊢[PRAAx] rationalLE x v)
    (hus : Γ ⊢[PRAAx] radius u s C D) (hvr : Γ ⊢[PRAAx] radius v r C D)
    (hsr : Γ ⊢[PRAAx] radius s r A B) : Γ ⊢[PRAAx]
    radius x r (A*D+C*B) (B*D) := by
  have lower : Γ ⊢[PRAAx] radius u r (A*D+C*B) (B*D) :=
    radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) (radius_triangle u s r C D A B hus hsr)
  have upper : Γ ⊢[PRAAx] radius v r (A*D+C*B) (B*D) :=
    radius_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (radius_triangle v r r C D A B hvr (radius_diagonal r A B))
  exact sandwich_radius u x v r _ _ hux hxv lower upper

theorem actual_raw_scalar_sandwich_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (((rationalLE (var 0) (var 1) ⋏ rationalLE (var 1) (var 2)) ⋏
      (radius (var 0) (var 3) (var 4) (var 5) ⋏ radius (var 2) (var 3) (var 4) (var 5))) ⟶
        radius (var 1) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (sandwich_radius _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_raw_perturbed_endpoint_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (((rationalLE (var 0) (var 1) ⋏ rationalLE (var 1) (var 2)) ⋏
      (radius (var 0) (var 3) (var 7) (var 8) ⋏
       (radius (var 2) (var 4) (var 7) (var 8) ⋏ radius (var 3) (var 4) (var 5) (var 6)))) ⟶
        radius (var 1) (var 4) (var 5*var 8+var 7*var 6) (var 6*var 8)) :=
  closeUniv 9 (.impI (perturbed_endpoints _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.RationalSandwichRadius
