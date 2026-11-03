import DiophantineConsistency.TenPositiveTrace75
import DiophantineConsistency.WeightedExpressionDegree

/-! # Literal syntax of the ten-positive 75/402 trace equation

`expression p` is the circuit `trace75_degree402.json` of package 163 as a
literal `Expr (Fin 10)`: the generic register map `TenPositiveTrace75.regs`
read in `Expr`, with the ports as integer constants and the ten unknowns as
variables. The DAG is never unfolded into a tree. Each register's
evaluation is proved from the previous ones (`ev_*`), so the proof of
`evalRing_expression` is linear in the 75 rows. This module imports neither
Foundation nor Mathlib's matrices. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace75

/-- The fixed ports as integer constants. -/
def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 10) := fun j => .constant (p j)

/-- The literal 75-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 9` are `J, F, alpha, i, T, w, s, n, eta, zeta`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 10) := value75 (ports p) Expr.var

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 10 → R)
local notation "𝓔" => regs (ports p) Expr.var
local notation "𝓟" => regs (fun j => (p j : R)) v

theorem ev_h : ((𝓔).h).evalRing v = (𝓟).h := by
  rw [h_def, h_def]
  simp only [ports, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one]

theorem ev_q : ((𝓔).q).evalRing v = (𝓟).q := by
  rw [q_def, q_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h]

theorem ev_Y : ((𝓔).Y).evalRing v = (𝓟).Y := by
  rw [Y_def, Y_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_C : ((𝓔).C).evalRing v = (𝓟).C := by
  rw [C_def, C_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_X : ((𝓔).X).evalRing v = (𝓟).X := by
  rw [X_def, X_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_k : ((𝓔).k).evalRing v = (𝓟).k := by
  rw [k_def, k_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one]

theorem ev_c : ((𝓔).c).evalRing v = (𝓟).c := by
  rw [c_def, c_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_k, ev_Y]

theorem ev_Am1 : ((𝓔).Am1).evalRing v = (𝓟).Am1 := by
  rw [Am1_def, Am1_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_Y]

theorem ev_A : ((𝓔).A).evalRing v = (𝓟).A := by
  rw [A_def, A_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Am1]

theorem ev_H : ((𝓔).H).evalRing v = (𝓟).H := by
  rw [H_def, H_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Am1]

theorem ev_E : ((𝓔).E).evalRing v = (𝓟).E := by
  rw [E_def, E_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_Y, ev_k]

theorem ev_rank : ((𝓔).rank).evalRing v = (𝓟).rank := by
  rw [rank_def, rank_def]
  simp only [ports, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_q]

theorem ev_e : ((𝓔).e).evalRing v = (𝓟).e := by
  rw [e_def, e_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_k, ev_rank]

theorem ev_B : ((𝓔).B).evalRing v = (𝓟).B := by
  rw [B_def, B_def]
  simp only [ports, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_C]

theorem ev_U : ((𝓔).U).evalRing v = (𝓟).U := by
  rw [U_def, U_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_c]

theorem ev_Delta : ((𝓔).Delta).evalRing v = (𝓟).Delta := by
  rw [Delta_def, Delta_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Am1]

theorem ev_a : ((𝓔).a).evalRing v = (𝓟).a := by
  rw [a_def, a_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Delta, ev_U, ev_E]

theorem ev_F0 : ((𝓔).F0).evalRing v = (𝓟).F0 := by
  rw [F0_def, F0_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_a]

theorem ev_f : ((𝓔).f).evalRing v = (𝓟).f := by
  rw [f_def, f_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_a, ev_F0]

theorem ev_Q : ((𝓔).Q).evalRing v = (𝓟).Q := by
  rw [Q_def, Q_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Delta, ev_a, ev_F0]

theorem ev_b : ((𝓔).b).evalRing v = (𝓟).b := by
  rw [b_def, b_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_c, ev_rank]

theorem ev_V : ((𝓔).V).evalRing v = (𝓟).V := by
  rw [V_def, V_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_f, ev_b, ev_c]

theorem ev_K : ((𝓔).K).evalRing v = (𝓟).K := by
  rw [K_def, K_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_c]

theorem ev_D : ((𝓔).D).evalRing v = (𝓟).D := by
  rw [D_def, D_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_Y]

theorem ev_Z : ((𝓔).Z).evalRing v = (𝓟).Z := by
  rw [Z_def, Z_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_X, ev_Y, ev_H, ev_V, ev_B, ev_K, ev_e]

theorem ev_M : ((𝓔).M).evalRing v = (𝓟).M := by
  rw [M_def, M_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_X, ev_Y, ev_H]

theorem ev_Gn : ((𝓔).Gn).evalRing v = (𝓟).Gn := by
  rw [Gn_def, Gn_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_E, ev_F0]

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression :
    (expression p).evalRing v = value75 (fun j => (p j : R)) v := by
  rw [expression, value75_def, value75_def]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, ev_Q, ev_Z, ev_M, ev_Gn, ev_V]

end Eval

end DiophantineConsistency.TenPositiveTrace75
