import DiophantineConsistency.P113.P113Value
import DiophantineConsistency.P138.P138EarlyFold

/-! # Package 113's front is package 138's

The registers `J q W X Y a H Δ F R η` of package 113 (`P113Value.regs p x`) are those of
package 138's front `P138Value.regsK p (front x) k` at the first eleven unknowns
(`front x i = x i` for `i < 11`; 138's last unknown is not read by the front) and at the `k` slot
`k = R + 1 + h X Y`. Up to operand order:

* the front registers agree (`J_eq` … `eta_eq`);
* 138's first norm `Dt = 1 + L (k + L)`, `L = X Y · Y k`, is 113's `E = 1 + ℓ(ℓ + 1) k²`,
  `ℓ = X Y²` (`Dt_eq`);
* 138's projector register `Kq = X (X + 2 a c) − 1` is 113's `K` (`Kq_eq`).

So every lemma of package 138 that reads only the front applies to package 113. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.P113Front

section Front
variable {𝔸 : Type*}

/-- The first eleven unknowns. -/
def front (x : Fin 12 → 𝔸) : Fin 11 → 𝔸 := fun i => x i.castSucc

variable (x : Fin 12 → 𝔸)

theorem front_0 : front x 0 = x 0 := rfl
theorem front_1 : front x 1 = x 1 := rfl
theorem front_2 : front x 2 = x 2 := rfl
theorem front_3 : front x 3 = x 3 := rfl
theorem front_4 : front x 4 = x 4 := rfl
theorem front_5 : front x 5 = x 5 := rfl
theorem front_6 : front x 6 = x 6 := rfl
theorem front_7 : front x 7 = x 7 := rfl
theorem front_8 : front x 8 = x 8 := rfl
theorem front_9 : front x 9 = x 9 := rfl
theorem front_10 : front x 10 = x 10 := rfl

end Front

section Generic
variable {𝔸 : Type*} [CommRing 𝔸]

/-- The `k` slot of package 138's front: 113's native index. -/
def kk (p : Fin 6 → 𝔸) (x : Fin 12 → 𝔸) : 𝔸 := (P113Value.regs p x).k

variable (p : Fin 6 → 𝔸) (x : Fin 12 → 𝔸)

local notation "𝓠" => P113Value.regs p x
local notation "𝓡" => P138Value.regsK p (front x) (kk p x)

theorem J_eq : (𝓠).J = (𝓡).J := by
  rw [P113Value.J_def, P138Value.J_def, front_0]; ring

theorem q_eq : (𝓠).q = (𝓡).q := by
  rw [P113Value.q_def, P138Value.q_def, P138Value.qm_def, J_eq]; ring

theorem W_eq : (𝓠).W0 = (𝓡).W := by
  rw [P113Value.W0_def, P138Value.W_def, front_6]; ring

theorem X_eq : (𝓠).X = (𝓡).X := by
  rw [P113Value.X_def, P138Value.X_def, q_eq, W_eq]

theorem Y_eq : (𝓠).Y = (𝓡).Y := by
  rw [P113Value.Y_def, P138Value.Y_def, P138Value.q3_def, P138Value.q2_def, q_eq, front_5]; ring

theorem a_eq : (𝓠).a = (𝓡).a := by
  rw [P113Value.a_def, P138Value.a_def, P138Value.E_def, X_eq, Y_eq]; ring

theorem H_eq : (𝓠).H = (𝓡).H := by
  rw [P113Value.H_def, P138Value.H_def, a_eq]

theorem Delta_eq : (𝓠).Delta = (𝓡).Delta := by
  rw [P113Value.Delta_def, P138Value.Delta_def, a_eq, H_eq]; ring

theorem F_eq : (𝓠).F = (𝓡).F := by
  rw [P113Value.F_def, P138Value.F_def, W_eq, q_eq, P138Value.q_def, front_1, front_2]; ring

theorem R_eq : (𝓠).R = (𝓡).R := by
  rw [P113Value.R_def, P138Value.R_def, P138Value.q2_def, q_eq, F_eq, J_eq, front_1]; ring

theorem k_eq : (𝓡).k = (𝓠).k := P138Value.k_reg p (front x) _

theorem eta_eq : (𝓠).eta = (𝓡).eta := by
  rw [P113Value.eta_def, P138Value.eta_def, P138Value.Yk_def, Y_eq, k_eq, front_8]

theorem Dt_eq : (𝓡).Dt = (𝓠).E := by
  rw [P138Value.Dt_def, P138Value.L_def, P138Value.E_def, P138Value.Yk_def, k_eq, ← X_eq,
    ← Y_eq, P113Value.E_def, P113Value.ell_def]
  ring

end Generic

section Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ModelDifferenceRing
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (p : Fin 6 → DiffRing V) (x : Fin 12 → DiffRing V)

/-- 138's projector register is 113's `K`. -/
theorem Kq_eq : P138EarlyFold.Kq p (front x) (kk p x) = (P113Value.regs p x).K := by
  unfold P138EarlyFold.Kq
  rw [P113Value.K_def, ← X_eq, ← a_eq, front_8]

end Model

#print axioms Dt_eq
#print axioms Kq_eq

end DiophantineConsistency.P113Front
