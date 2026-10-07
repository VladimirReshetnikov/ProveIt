import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

def layerTailDegree (m : ℕ) : ℕ := m * (2^(m+1)+1)

theorem le_layerTailDegree (m : ℕ) : m ≤ layerTailDegree m := by
  unfold layerTailDegree
  nlinarith [Nat.zero_le (2^(m+1))]

theorem layerDegree_le_tailDegree {m : ℕ} (j : Fin m) : j.val+1 ≤ layerTailDegree m :=
  (Nat.succ_le_of_lt j.isLt).trans (le_layerTailDegree m)

theorem layerTailDegree_dominates {m h q r : ℕ}
    (hh : h ≤ m) (hq : q ≤ m+1) (hr : r ≤ 2^q) :
    h*(r+1) < layerTailDegree m+1 := by
  apply Nat.lt_succ_of_le
  exact Nat.mul_le_mul hh (Nat.add_le_add_right
    (hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)) 1)

theorem layerTailDegree_row_bound {m h : ℕ} {α O : Type*}
    [Fintype α] [Fintype O] (rows : O → Finset α) (hinj : Function.Injective rows)
    (hh : h ≤ m) (hq : Fintype.card α ≤ m+1) :
    h*(Fintype.card O+1) < layerTailDegree m+1 := by
  apply layerTailDegree_dominates hh hq
  simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj

end Erdos3

end

end OAI
