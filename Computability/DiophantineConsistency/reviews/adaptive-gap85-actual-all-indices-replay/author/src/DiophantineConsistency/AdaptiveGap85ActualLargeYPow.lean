import DiophantineConsistency.AdaptiveGap85ActualAllIndicesRoot
import DiophantineConsistency.AdaptiveGap85LargeYPow
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85ActualLargeYPow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticPellRecurrence AdaptiveGap85Literal
open AdaptiveGap85ActualAllIndicesRoot AdaptiveGap85LargeYPow
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An actual 85-zero has an internal main index at which the large-Y
condition forces X to be its represented power of two. -/
theorem actual_zero_large_Y_forces_power (p : Fin 4 → ℕ) (v : Fin 13 → V)
    (hb : 0<(p 0:V)) (hv : ∀ j,0<v j)
    (hz : InternalZero (expressionAt85 (fun j => (p j:ℤ))) v) :
    ∃ m : V, 0<m ∧ ycoord m (v 6*v 7+v 7)=v 9+v 7*(v 9+v 10) ∧
      (7*Exp.exp m≤v 7 → v 6=Exp.exp m) := by
  obtain ⟨m,hm,hc,hcong⟩ := actual_zero_root_congruences p v hb hv hz
  exact ⟨m,hm,hc,fun hY => large_Y_forces_equal (v 6) (v 7) (Exp.exp m) (one_le_exp m) hY hcong⟩
end DiophantineConsistency.AdaptiveGap85ActualLargeYPow
