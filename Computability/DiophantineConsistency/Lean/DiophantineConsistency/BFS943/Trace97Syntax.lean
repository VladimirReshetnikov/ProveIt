import DiophantineConsistency.BFS943.Trace97Regs
import DiophantineConsistency.BFS943.Centred87Syntax

/-! # Literal syntax of the ten-positive 97/202 `quotient_t` equation

`expression p` is the circuit `quotient_t_radix67.json` of package 194 as a
literal `Expr (Fin 10)`: `TenPositiveTrace97.value97` read in `Expr`, with the
ports as integer constants and the ten unknowns as variables. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace97
open TenPositiveTrace87 (ports ev_Am1 ev_U ev_E ev_q ev_k ev_X ev_Y ev_Q ev_M ev_Gn ev_V)

/-- The literal 97-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value97 (ports p) Expr.var

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R)

theorem ev_centre : (centre (ports p) Expr.var).evalRing v = centre (fun j => (p j : R)) v := by
  simp only [centre, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_var, Nat.cast_ofNat, ev_Am1, ev_U, ev_E, ev_q, ev_k, ev_X, ev_Y]

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression :
    (expression p).evalRing v = value97 (fun j => (p j : R)) v := by
  rw [expression, value97_scaled, value97_scaled]
  simp only [TenPositiveScaled87.scaledNorm, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_ofNat, Nat.cast_ofNat, ev_Q, ev_M, ev_Gn, ev_V,
    TenPositiveCentred87.ev_Z, ev_centre]

end Eval

end DiophantineConsistency.TenPositiveTrace97

namespace Trace97BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace97
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=
  TenPositiveTrace97.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    InternalZero (literal p) v ↔
      value97 (Trace87Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace97.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace97BFSSyntax.literal_zero_iff
end Trace97BFSSyntax
