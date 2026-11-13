import DiophantineConsistency.BFS943.Trace111Regs
import DiophantineConsistency.BFS943.Trace87Syntax

/-! # Literal syntax of the ten-positive 111/198 `product2` equation

`expression p` is the circuit `product2_radix67.json` of package 194 as a
literal `Expr (Fin 10)`: `TenPositiveTrace111.value111` read in `Expr`, with
the ports as integer constants and the ten unknowns as variables. The
carrier evaluation `ev_regsW_Z` is that of `TenPositiveScaled87.regsW`. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace111
open TenPositiveTrace87 (ports ev_h ev_D ev_H ev_V ev_b ev_B ev_K ev_ecl ev_Q ev_M ev_Gn
  ev_Am1 ev_U ev_E ev_q ev_k ev_X ev_Y ev_c)

/-- The literal 111-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value111 (ports p) Expr.var

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R)

theorem ev_regsW_Z (ws : Expr (Fin 10)) :
    ((TenPositiveScaled87.regsW (ports p) Expr.var ws).Z).evalRing v =
      (TenPositiveScaled87.regsW (fun j => (p j : R)) v (ws.evalRing v)).Z := by
  rw [TenPositiveScaled87.regsW_Z_def, TenPositiveScaled87.regsW_Z_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_D, ev_H,
    ev_V, ev_b, ev_B, ev_K, ev_ecl]

theorem ev_omega : (omega (ports p) Expr.var).evalRing v = omega (fun j => (p j : R)) v := by
  simp only [omega, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_var, Nat.cast_ofNat, Nat.cast_one, ev_Am1, ev_U, ev_E, ev_q, ev_k, ev_X, ev_Y,
    ev_V, ev_b, ev_c]

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression :
    (expression p).evalRing v = value111 (fun j => (p j : R)) v := by
  rw [expression, value111_scaled, value111_scaled]
  simp only [TenPositiveScaled87.scaledNorm, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_ofNat, Nat.cast_ofNat, ev_Q, ev_M, ev_Gn, ev_V,
    ev_regsW_Z, ev_omega]

end Eval

end DiophantineConsistency.TenPositiveTrace111

namespace Trace111BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace111
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=
  TenPositiveTrace111.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    InternalZero (literal p) v ↔
      value111 (Trace87Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace111.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace111BFSSyntax.literal_zero_iff
end Trace111BFSSyntax
