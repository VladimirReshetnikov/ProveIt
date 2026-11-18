import IPRADerivations.Analysis.GaussianRootMembershipBudget

/-!
# Exact two-name order budget for the sharp root-distance residual

A distance-name upper observation is n/d+1/H. Applying the sharp
fixed-radius residual cut gives M(n/d+1/H)+A/B+1/h. The actual normalized
linear-distance name has value Mn/d+A/B; M J<=H supplies its prescribed
error 1/J. This is the natural cross-product inequality for that precise
two-name comparison. All inputs, including M=0, remain numerical terms.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRootDistanceOrderBudget

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem radius_budget (M nu d A B h H J : PTm n) (hM : Γ ⊢[PRAAx] le (M*J) H) : Γ ⊢[PRAAx]
    le (((M*(nu*H+d)*B+A*(d*H))*h+(d*H)*B)*((B*d)*h*J))
      (((M*nu*B+A*d)*h*J+(B*d)*(J+h))*(((d*H)*B)*h)) := by
  have scaled := mul_le_mul_right ((B*d*h)*(B*d*h)) hM
  have common := le_refl (Γ := Γ) (((M*nu*B+A*d)*h+B*d)*(B*d*h*H*J))
  exact le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ scaled common)

theorem root_distance_order_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (le (var 0*var 7) (var 6) ⟶
      le (((var 0*(var 1*var 6+var 2)*var 4+var 3*(var 2*var 6))*var 5+(var 2*var 6)*var 4)*
          ((var 4*var 2)*var 5*var 7))
        (((var 0*var 1*var 4+var 3*var 2)*var 5*var 7+(var 4*var 2)*(var 7+var 5))*
          (((var 2*var 6)*var 4)*var 5))) :=
  closeUniv 8 (.impI (radius_budget _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianRootDistanceOrderBudget
