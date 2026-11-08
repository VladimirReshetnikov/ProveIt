import DiophantineConsistency.BFS943.Trace89Regs
import DiophantineConsistency.BFS943.Centred87Syntax

/-! # Literal syntax of the ten-positive 89/210 centred equation

`expression p` is the circuit `centerAp1_radix67.json` of package 179 as a
literal `Expr (Fin 10)`: `TenPositiveTrace89.value89` read in `Expr`, with the
ports as integer constants and the ten unknowns as variables. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace89
open TenPositiveTrace87 (ports ev_Am1 ev_U ev_E)

/-- The literal 89-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value89 (ports p) Expr.var

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R)

theorem ev_centre : (centre (ports p) Expr.var).evalRing v = centre (fun j => (p j : R)) v := by
  change (((TenPositiveTrace87.regs (ports p) Expr.var).Am1 + 2) *
      ((TenPositiveTrace87.regs (ports p) Expr.var).U *
        (TenPositiveTrace87.regs (ports p) Expr.var).E)).evalRing v =
    ((TenPositiveTrace87.regs (fun j => (p j : R)) v).Am1 + 2) *
      ((TenPositiveTrace87.regs (fun j => (p j : R)) v).U *
        (TenPositiveTrace87.regs (fun j => (p j : R)) v).E)
  simp only [Expr.evalRing_add, Expr.evalRing_mul, Expr.evalRing_ofNat, Nat.cast_ofNat,
    ev_Am1, ev_U, ev_E]

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression :
    (expression p).evalRing v = value89 (fun j => (p j : R)) v := by
  rw [expression, value89, value89, TenPositiveCentred87.evalRing_valueAt, ev_centre]

end Eval

end DiophantineConsistency.TenPositiveTrace89

namespace Trace89BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace89
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 10) :=
  TenPositiveTrace89.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    InternalZero (literal p) v ↔
      value89 (Trace87Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace89.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace89BFSSyntax.literal_zero_iff
end Trace89BFSSyntax
