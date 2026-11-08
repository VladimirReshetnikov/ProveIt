import DiophantineConsistency.BFS943.Centred87Regs
import DiophantineConsistency.BFS943.Trace87Syntax

/-! # Literal syntax of the centred 87 registers

`TenPositiveCentred87.regsAt` and `valueAt` read in `Expr (Fin 10)` at the
literal ports `TenPositiveTrace87.ports p` evaluate, in every commutative ring,
to the same maps at the evaluated centre (`evalRing_valueAt`). The register
evaluations are `Trace87Syntax`'s `ev_*`; only the centred carrier is new. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveCentred87
open TenPositiveTrace87 (ports ev_h ev_D ev_H ev_V ev_b ev_B ev_K ev_ecl ev_Q ev_M ev_Gn)

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R)

theorem ev_Z (g : Expr (Fin 10)) :
    ((regsAt (ports p) Expr.var g).Z).evalRing v =
      (regsAt (fun j => (p j : R)) v (g.evalRing v)).Z := by
  rw [Z_def, Z_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_D, ev_H,
    ev_V, ev_b, ev_B, ev_K, ev_ecl]

theorem evalRing_valueAt (g : Expr (Fin 10)) :
    (valueAt (ports p) Expr.var g).evalRing v =
      valueAt (fun j => (p j : R)) v (g.evalRing v) := by
  rw [valueAt_norm, valueAt_norm]
  simp only [TenPositiveTrace76.normValue, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, ev_Q, ev_Z, ev_M, ev_Gn, ev_V]

end Eval

end DiophantineConsistency.TenPositiveCentred87
