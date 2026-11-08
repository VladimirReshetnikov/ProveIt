import DiophantineConsistency.BFS943.Trace104Regs
import DiophantineConsistency.BFS943.Trace104Factors
import DiophantineConsistency.WeightedExpressionDegree

/-! # Literal syntax of the eleven-positive 104/174 constant-dilation equation

`expression p` is package 184's circuit `compact11/constant_dilation11.json` as
a literal `Expr (Fin 11)`: `TenPositiveTrace104.value104` read in `Expr`, with
the ports as integer constants and the eleven unknowns
`J, F, α, i, T, w, s, n, η, ζ, κ` as variables `0, …, 10`. The register
evaluations `ev_*` are those of `Trace87Syntax`, stated at an arbitrary
variable map `u` of the ten core unknowns (here `core Expr.var`). -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
namespace DiophantineConsistency.TenPositiveTrace104

/-- The fixed ports as integer constants. -/
def ports (p : Fin 4 → ℤ) : Fin 4 → Expr (Fin 11) := fun j => .constant (p j)

/-- The literal 104-operation polynomial at ports `p = (beta, K0, MC, MF)`; its
variables `0, …, 10` are `J, F, alpha, i, T, w, s, n, eta, zeta, kappa`. -/
def expression (p : Fin 4 → ℤ) : Expr (Fin 11) := value104 (ports p) Expr.var

/-- The core variable map evaluated at an eleven-coordinate valuation. -/
def ev {R : Type*} [CommRing R] (u : Fin 10 → Expr (Fin 11)) (v : Fin 11 → R) : Fin 10 → R :=
  fun j => (u j).evalRing v

section Eval
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (u : Fin 10 → Expr (Fin 11)) (v : Fin 11 → R)
local notation "𝓔" => regs (ports p) u
local notation "𝓟" => regs (fun j => (p j : R)) (ev u v)

theorem ev_h : ((𝓔).h).evalRing v = (𝓟).h := by
  rw [h_def, h_def]
  simp only [ev, ports, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one]

theorem ev_q : ((𝓔).q).evalRing v = (𝓟).q := by
  rw [q_def, q_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h]

theorem ev_Y : ((𝓔).Y).evalRing v = (𝓟).Y := by
  rw [Y_def, Y_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_C : ((𝓔).C).evalRing v = (𝓟).C := by
  rw [C_def, C_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_X : ((𝓔).X).evalRing v = (𝓟).X := by
  rw [X_def, X_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_k : ((𝓔).k).evalRing v = (𝓟).k := by
  rw [k_def, k_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one]

theorem ev_c : ((𝓔).c).evalRing v = (𝓟).c := by
  rw [c_def, c_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_k, ev_Y]

theorem ev_Am1 : ((𝓔).Am1).evalRing v = (𝓟).Am1 := by
  rw [Am1_def, Am1_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_Y]

theorem ev_A : ((𝓔).A).evalRing v = (𝓟).A := by
  rw [A_def, A_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Am1]

theorem ev_H : ((𝓔).H).evalRing v = (𝓟).H := by
  rw [H_def, H_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Am1]

theorem ev_E : ((𝓔).E).evalRing v = (𝓟).E := by
  rw [E_def, E_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_Y, ev_k]

theorem ev_rank : ((𝓔).rank).evalRing v = (𝓟).rank := by
  rw [rank_def, rank_def]
  simp only [ev, ports, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_q]

theorem ev_e : ((𝓔).e).evalRing v = (𝓟).e := by
  rw [e_def, e_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_k, ev_rank]

theorem ev_B : ((𝓔).B).evalRing v = (𝓟).B := by
  rw [B_def, B_def]
  simp only [ev, ports, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_C, ev_q]

theorem ev_U : ((𝓔).U).evalRing v = (𝓟).U := by
  rw [U_def, U_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_c]

theorem ev_Delta : ((𝓔).Delta).evalRing v = (𝓟).Delta := by
  rw [Delta_def, Delta_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Am1]

theorem ev_a : ((𝓔).a).evalRing v = (𝓟).a := by
  rw [a_def, a_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Delta, ev_U, ev_E]

theorem ev_F0 : ((𝓔).F0).evalRing v = (𝓟).F0 := by
  rw [F0_def, F0_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_a]

theorem ev_f : ((𝓔).f).evalRing v = (𝓟).f := by
  rw [f_def, f_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_a, ev_F0]

theorem ev_Q : ((𝓔).Q).evalRing v = (𝓟).Q := by
  rw [Q_def, Q_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_Delta, ev_a, ev_F0]

theorem ev_b : ((𝓔).b).evalRing v = (𝓟).b := by
  rw [b_def, b_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_c, ev_rank]

theorem ev_V : ((𝓔).V).evalRing v = (𝓟).V := by
  rw [V_def, V_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_f, ev_b, ev_c]

theorem ev_K : ((𝓔).K).evalRing v = (𝓟).K := by
  rw [K_def, K_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_X, ev_c]

theorem ev_D : ((𝓔).D).evalRing v = (𝓟).D := by
  rw [D_def, D_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_q]

theorem ev_ecl : (ecl (ports p) u).evalRing v = ecl (fun j => (p j : R)) (ev u v) := by
  rw [ecl_def, ecl_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_e, ev_q, ev_X, ev_Y, ev_k]

theorem ev_Z : ((𝓔).Z).evalRing v = (𝓟).Z := by
  rw [Z_def, Z_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_D, ev_H, ev_b, ev_V, ev_B, ev_K, ev_ecl]

theorem ev_M : ((𝓔).M).evalRing v = (𝓟).M := by
  rw [M_def, M_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_h, ev_D, ev_H]

theorem ev_Gn : ((𝓔).Gn).evalRing v = (𝓟).Gn := by
  rw [Gn_def, Gn_def]
  simp only [ev, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat, Expr.evalRing_var, Expr.evalRing_constant, Nat.cast_ofNat, Nat.cast_one, ev_E, ev_F0]

end Eval

theorem ev_core {R : Type*} [CommRing R] (v : Fin 11 → R) :
    ev (core (Expr.var : Fin 11 → Expr (Fin 11))) v = core v := rfl

/-- The literal syntax evaluates to the circuit value in every commutative ring. -/
theorem evalRing_expression {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 11 → R) :
    (expression p).evalRing v = value104 (fun j => (p j : R)) v := by
  simp only [expression, value104]
  simp only [Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_ofNat,
    Expr.evalRing_var, Nat.cast_ofNat, Nat.cast_one, ev_Q, ev_V, ev_Gn, ev_h, ev_D, ev_b, ev_B,
    ev_K, ev_H, ev_ecl, ev_core]

end DiophantineConsistency.TenPositiveTrace104

namespace Trace104BFSSyntax
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing TenPositiveTrace104
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def literal (p : Fin 4 → ℕ) : Expr (Fin 11) :=
  TenPositiveTrace104.expression (fun j => (p j : ℤ))

theorem literal_zero_iff (p : Fin 4 → ℕ) (v : Fin 11 → V) :
    InternalZero (literal p) v ↔
      value104 (Trace104Factors.ports p) (fun j => ι (v j)) = 0 := by
  rw [internalZero_iff]
  unfold literal
  rw [TenPositiveTrace104.evalRing_expression]
  simp only [Int.cast_natCast]
  rfl

#print axioms Trace104BFSSyntax.literal_zero_iff
end Trace104BFSSyntax
