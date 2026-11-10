import DiophantineConsistency.TenPositiveTrace75Syntax
import DiophantineConsistency.BFS943.Trace77Circuit
import DiophantineConsistency.BFS943.Trace75Factors

/-! # Literal syntax of the ten-positive 77/348 trace equation

`TenPositiveTrace77.expression p` is the circuit
`171-pooled-powers-separated-radicals/positive/q4_interpolation/equation.json`
as a literal `Expr (Fin 10)`: `value77` read in `Expr`, with the ports as
integer constants and the ten unknowns as variables. Its evaluation reuses
the per-register lemmas `TenPositiveTrace75.ev_*`, so the proof is linear in
the rows. `literal_zero_iff` binds model zeros of the literal to `value77` at
the difference-ring ports. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section

namespace DiophantineConsistency.TenPositiveTrace77
open DiophantineConsistency.TenPositiveTrace75

/-- The literal 77-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value77 (TenPositiveTrace75.ports p) Expr.var

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R) :
    (expression p).evalRing v = value77 (fun j => (p j : R)) v := by
  rw [expression, value77_def, value77_def, Z77_def, Z77_def, M77_def, M77_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    ev_Q, ev_Gn, ev_V, ev_h, ev_q, ev_H, ev_b, ev_B, ev_K, ev_e]

end DiophantineConsistency.TenPositiveTrace77

namespace Trace77BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace77
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=
  TenPositiveTrace77.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    InternalZero (literal p) v ↔
      value77 (Trace75Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace77.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace77BFSSyntax.literal_zero_iff
end Trace77BFSSyntax
