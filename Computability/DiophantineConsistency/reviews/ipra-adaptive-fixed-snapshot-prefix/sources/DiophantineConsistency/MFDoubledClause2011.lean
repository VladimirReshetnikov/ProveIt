import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Bound
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Use
import Mathlib.Tactic.Zify

/-! Matrix-free doubled-clause mask proof. The ordinary doubled-clause module
reuses this independently maintained arithmetic theorem. -/
/-!
# Full doubled-clause decoding for the 2011-field presentation

This is arithmetic over natural numbers, independent of the physical stencil.
The incoming carry and both Boolean contributions remain present while the
34-bit word is decoded. In particular, no zero-carry hypothesis is used.
-/

namespace DiophantineConsistency.MF.DoubledClause2011

set_option Elab.async false

def mask : ℕ := 2 ^ 45 - 4

/-- The full mask tests precisely bits 2 through 44. -/
theorem mask_iff (x : ℕ) : x &&& mask = 0 ↔ x % 2 ^ 45 ≤ 3 := by
  have hd : (x &&& mask) / 4 = (x / 4) % 2 ^ 43 := by
    calc
      (x &&& mask) / 4 = (x &&& mask) / 2 / 2 := by
        rw [Nat.div_div_eq_div_mul]
      _ = (x / 2 / 2) &&& (2 ^ 43 - 1) := by
        rw [Nat.and_div_two, Nat.and_div_two]
        rfl
      _ = (x / 4) % 2 ^ 43 := by
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.div_div_eq_div_mul]
  have hm : (x &&& mask) % 4 = 0 := by
    change (x &&& mask) % 2 ^ 2 = 0
    rw [Nat.and_mod_two_pow]
    norm_num [mask]
  constructor
  · intro h
    rw [h] at hd
    norm_num at hd ⊢
    omega
  · intro h
    norm_num at hd h
    omega

end DiophantineConsistency.MF.DoubledClause2011
