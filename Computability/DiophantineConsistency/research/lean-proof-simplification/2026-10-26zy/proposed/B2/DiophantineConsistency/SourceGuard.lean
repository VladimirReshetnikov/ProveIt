import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Defs

/-! Arithmetic sign recovery for old and gap positive source solutions. -/

namespace DiophantineConsistency.SourceGuard

/-- A guard obtainable from either domain element need not be an external
parameter of the equivalence. Proof irrelevance aligns the inverse proofs. -/
def discharge {A B : Type*} {G : Prop} (e : G → A ≃ B)
    (ga : A → G) (gb : B → G) : A ≃ B where
  toFun a := e (ga a) a
  invFun b := (e (gb b)).symm b
  left_inv a := (e (ga a)).left_inv a
  right_inv b := (e (gb b)).right_inv b

/-- Shared sign argument. The final factor D is either L or 1+L. -/
theorem beta_pos_kernel {β J L N D : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N) (hD : 0 < D)
    (hquad : L = (1 + β * J)^2 - 1)
    (hlinear : N = (1 + β * J) * D) : 0 < β := by
  have hq : (0 : ℤ) < 1 + β * J :=
    (mul_pos_iff_of_pos_right hD).mp (hlinear ▸ hN)
  have hq1 : (1 : ℤ) < 1 + β * J := by
    by_contra h
    have he : (1 : ℤ) + β * J = 1 := by omega
    rw [he] at hquad
    norm_num at hquad
    omega
  have hp : 0 < β * J := by omega
  exact pos_of_mul_pos_left hp hJ

/-- Gap row 1 is N=qL. -/
theorem gap_rows_beta_pos {β J L N : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N)
    (hzero : L + ((-2) * β) * J + (-(β ^ 2)) * (J ^ 2) = 0)
    (hone : (-1) * L + N + (-β) * (J * L) = 0) : 0 < β := by
  apply beta_pos_kernel (D := L) hJ hL hN hL
  · linear_combination hzero
  · linear_combination hone

/-- Old row 1 is N=q(1+L). -/
theorem old_rows_beta_pos {β J L N : ℤ}
    (hJ : 0 ≤ J) (hL : 0 < L) (hN : 0 < N)
    (hzero : L + ((-2) * β) * J + (-(β ^ 2)) * (J ^ 2) = 0)
    (hone : (-1) + (-1) * L + N + (-β) * J + (-β) * (J * L) = 0) : 0 < β := by
  apply beta_pos_kernel (D := 1 + L) hJ hL hN (by omega)
  · linear_combination hzero
  · linear_combination hone

end DiophantineConsistency.SourceGuard
