import Diophantine.Paper1984.Masking
import DiophantineConsistency.MFNativeCyclicConvolution
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
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

/-! Matrix-free radix digit proofs used by local normalization and by
`DiophantineConsistency.NativeRadixDigits`. -/
/-! # Radix digit reconstruction and periodic finite words -/

namespace DiophantineConsistency.MF.NativeRadixDigits

open DiophantineConsistency.MF.NativeCyclicConvolution DiophantineConsistency.MF.Jones1982
open scoped BigOperators

variable {n : ℕ} [NeZero n]

theorem word_origin (r : ℕ) (a : ℕ) :
    word r (fun k : ZMod n => if k = 0 then a else 0) = a := by
  classical
  simp [word, ite_mul]

omit [NeZero n] in
theorem periodic_sum (r L N : ℕ) (hL : 0 < L) (a : Fin L → ℕ) :
    (∑ i : Fin (N * L), a ⟨i.val % L, Nat.mod_lt _ hL⟩ * r ^ i.val) =
      (∑ j : Fin L, a j * r ^ j.val) * (∑ k : Fin N, (r ^ L) ^ k.val) := by
  have he : (∑ p : Fin N × Fin L, a p.2 * r ^ (p.2.val + L * p.1.val)) =
      ∑ i : Fin (N * L), a ⟨i.val % L, Nat.mod_lt _ hL⟩ * r ^ i.val := by
    apply Fintype.sum_equiv finProdFinEquiv
    intro p
    simp only [finProdFinEquiv_apply_val, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt p.2.isLt]
  rw [← he, Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add, ← pow_mul]
  ring

end DiophantineConsistency.MF.NativeRadixDigits
