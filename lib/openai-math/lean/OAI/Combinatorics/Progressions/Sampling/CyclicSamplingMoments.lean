import OAI.Combinatorics.Progressions.Estimates.LocalShiftFiber

namespace OAI

section

namespace Erdos3.CyclicCrootSisask

open Finset
open scoped BigOperators

local notation:70 s:70 " ^^ " n:71 => Fintype.piFinset fun _ : Fin n ↦ s

variable {N k m : ℕ} [NeZero N]

theorem sum_setAverageTranslate_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (n : ℕ) :
    ∑ x, |setAverageTranslate A f x| ^ n ≤ ∑ x, |f x| ^ n := by
  have hc : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  cases n with
  | zero => simp
  | succ n =>
    have hpoint (x : ZMod N) : |setAverageTranslate A f x| ^ (n + 1) ≤
        (∑ a ∈ A, |f (x - a)| ^ (n + 1)) / A.card := by
      have habs : |setAverageTranslate A f x| ≤ (∑ a ∈ A, |f (x - a)|) / A.card := by
        rw [setAverageTranslate, abs_div, abs_of_pos hc]
        exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) hc.le
      have hj := pow_sum_div_card_le_sum_pow (s := A)
        (fun a _ => abs_nonneg (f (x - a))) n
      calc
        _ ≤ ((∑ a ∈ A, |f (x - a)|) / A.card) ^ (n + 1) :=
          pow_le_pow_left₀ (abs_nonneg _) habs _
        _ = (∑ a ∈ A, |f (x - a)|) ^ (n + 1) / (A.card : ℝ) ^ n / A.card := by
          rw [div_pow, pow_succ (A.card : ℝ) n, div_mul_eq_div_div]
        _ ≤ _ := div_le_div_of_nonneg_right hj hc.le
    calc
      _ ≤ ∑ x, (∑ a ∈ A, |f (x - a)| ^ (n + 1)) / A.card :=
        Finset.sum_le_sum (fun x _ => hpoint x)
      _ = (∑ a ∈ A, ∑ x, |f (x - a)| ^ (n + 1)) / A.card := by
        rw [← Finset.sum_div, Finset.sum_comm]
      _ = (∑ _a ∈ A, ∑ x, |f x| ^ (n + 1)) / A.card := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        exact Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
      _ = _ := by simp [hc.ne']

theorem sum_centeredTranslate_pow_le {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (a : ZMod N) (hm : m ≠ 0) :
    ∑ x, |centeredTranslate A f x a| ^ (2 * m) ≤
      2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m) := by
  have hpoint (x : ZMod N) : |centeredTranslate A f x a| ^ (2 * m) ≤
      2 ^ (2 * m - 1) * (|f (x - a)| ^ (2 * m) + |setAverageTranslate A f x| ^ (2 * m)) := by
    apply (pow_le_pow_left₀ (abs_nonneg _) (abs_sub _ _) _).trans
    exact add_pow_le (abs_nonneg _) (abs_nonneg _) _
  have hshift : (∑ x, |f (x - a)| ^ (2 * m)) = ∑ x, |f x| ^ (2 * m) :=
    Fintype.sum_equiv (Equiv.subRight a) _ _ (fun _ => rfl)
  calc
    _ ≤ ∑ x, 2 ^ (2 * m - 1) *
        (|f (x - a)| ^ (2 * m) + |setAverageTranslate A f x| ^ (2 * m)) :=
      Finset.sum_le_sum (fun x _ => hpoint x)
    _ = 2 ^ (2 * m - 1) * ((∑ x, |f x| ^ (2 * m)) +
        ∑ x, |setAverageTranslate A f x| ^ (2 * m)) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, hshift]
    _ ≤ 2 ^ (2 * m - 1) * ((∑ x, |f x| ^ (2 * m)) + ∑ x, |f x| ^ (2 * m)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add le_rfl (sum_setAverageTranslate_pow_le hA f _)) (by positivity)
    _ = _ := by
      rw [← pow_sub_one_mul (show 2 * m ≠ 0 by omega) (2 : ℝ)]
      ring

theorem global_sampleDeviation_input_moment {A : Finset (ZMod N)} (hA : A.Nonempty)
    (f : ZMod N → ℝ) (hm : m ≠ 0) :
    ∑ a ∈ A ^^ k, ∑ x, |sampleDeviation A f a x| ^ (2 * m) ≤
      (8 * m) ^ m * k ^ (m - 1) * (A.card : ℝ) ^ k * k *
        (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
  apply (global_sampleDeviation_moment (k := k) hA f hm).trans
  have hsum (a : Fin k → ZMod N) :
      ∑ x, ∑ i, |centeredTranslate A f x (a i)| ^ (2 * m) ≤
        k * (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : Fin k, 2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m) :=
        Finset.sum_le_sum (fun i _ => sum_centeredTranslate_pow_le hA f (a i) hm)
      _ = _ := by simp
  calc
    _ ≤ (8 * m) ^ m * k ^ (m - 1) *
        ∑ _a ∈ A ^^ k, k * (2 ^ (2 * m) * ∑ x, |f x| ^ (2 * m)) := by
      apply mul_le_mul_of_nonneg_left
      · exact Finset.sum_le_sum (fun a _ => hsum a)
      · positivity
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_piFinset_const, Nat.cast_pow]
      ring

end Erdos3.CyclicCrootSisask

end

end OAI
