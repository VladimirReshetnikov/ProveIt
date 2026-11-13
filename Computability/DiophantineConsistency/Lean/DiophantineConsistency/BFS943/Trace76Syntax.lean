import DiophantineConsistency.TenPositiveTrace75Syntax
import DiophantineConsistency.BFS943.Trace76Circuit
import DiophantineConsistency.BFS943.Trace75Factors

/-! # Literal syntax of the ten-positive 76/352 trace equation

`TenPositiveTrace76.expression p` is the circuit `trace76_degree352.json` of
package 163 as a literal `Expr (Fin 10)`: `value76` read in `Expr`, with the
ports as integer constants and the ten unknowns as variables. Its
evaluation reuses the per-register lemmas `TenPositiveTrace75.ev_*`, so the
proof is linear in the rows. `literal_zero_iff` binds model zeros of the
literal to `value76` at the difference-ring ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section

namespace DiophantineConsistency.TenPositiveTrace76
open DiophantineConsistency.TenPositiveTrace75

/-- The literal 76-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value76 (TenPositiveTrace75.ports p) Expr.var

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R) :
    (expression p).evalRing v = value76 (fun j => (p j : R)) v := by
  rw [expression, value76_norm, value76_norm, normValue, normValue, Z76_def, Z76_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    ev_Q, ev_M, ev_Gn, ev_V, ev_h, ev_D, ev_H, ev_b, ev_B, ev_K, ev_e]

end DiophantineConsistency.TenPositiveTrace76

namespace Trace76BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace76
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=
  TenPositiveTrace76.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    InternalZero (literal p) v ↔
      value76 (Trace75Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace76.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace76BFSSyntax.literal_zero_iff
end Trace76BFSSyntax
