import DiophantineConsistency.BFS943.Trace118Regs
import DiophantineConsistency.BFS943.Trace87Syntax

/-! # Literal syntax of the ten-positive 118/190 `whole190` equation

`expression p` is the circuit `whole190.json` of package 193 as a literal
`Expr (Fin 10)`: `TenPositiveTrace118.value118` read in `Expr`, with the ports
as integer constants and the ten unknowns as variables. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace118
open TenPositiveTrace87 (ports ev_h ev_D ev_H ev_V ev_b ev_B ev_K ev_ecl ev_Q ev_M ev_Gn
  ev_Am1 ev_U ev_E ev_k ev_X ev_Y ev_c)

/-- The literal 118-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value118 (ports p) Expr.var

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R)

theorem ev_omegaFold :
    (omegaFold (ports p) Expr.var).evalRing v = omegaFold (fun j => (p j : R)) v := by
  simp only [omegaFold, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_ofNat, Nat.cast_ofNat, Nat.cast_one, ev_Am1, ev_U, ev_E, ev_k, ev_X, ev_Y,
    ev_V, ev_b, ev_B, ev_c]

theorem ev_regs118_Z :
    ((regs118 (ports p) Expr.var).Z).evalRing v = (regs118 (fun j => (p j : R)) v).Z := by
  rw [regs118_Z_def, regs118_Z_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_var, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_D, ev_H, ev_B, ev_K, ev_ecl,
    ev_omegaFold]

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression :
    (expression p).evalRing v = value118 (fun j => (p j : R)) v := by
  rw [expression, value118_norm, value118_norm]
  simp only [norm16, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_ofNat, Nat.cast_ofNat, ev_Q, ev_M, ev_Gn, ev_V, ev_regs118_Z]

end Eval

end DiophantineConsistency.TenPositiveTrace118

namespace Trace118BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace118
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=
  TenPositiveTrace118.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    InternalZero (literal p) v ↔
      value118 (Trace87Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace118.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace118BFSSyntax.literal_zero_iff
end Trace118BFSSyntax
