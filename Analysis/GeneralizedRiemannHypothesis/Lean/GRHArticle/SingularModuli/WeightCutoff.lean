import GRHArticle.SingularModuli.FactorialThreshold
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.SuccPred.Archimedean

/-!
# Existence of the greatest admissible factorial-weight index

A positive linear lower bound on the weights makes the index set in the local
root count bounded above. An initial weight witnesses that it is nonempty.
-/

namespace GRHArticle.SingularModuli

/-- The factorial weights have a linear lower bound from Legendre's formula. -/
theorem factorialWeight_linear_le {p : ℕ} [hp : Fact (Nat.Prime p)] (r : ℚ) (k : ℕ) :
    (r - 1 / ((p : ℚ) - 1)) * k ≤ factorialWeight p r k := by
  have hp₁ : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hval : (p - 1) * padicValNat p k.factorial ≤ k := by
    by_cases hk : k = 0
    · simp [hk]
    · exact (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hk).le
  have hq : ((p - 1 : ℕ) : ℚ) * (padicValNat p k.factorial : ℚ) ≤ (k : ℚ) := by
    exact_mod_cast hval
  rw [Nat.cast_sub hp.out.one_lt.le, Nat.cast_one, mul_comm] at hq
  have hbound : (padicValNat p k.factorial : ℚ) ≤ (k : ℚ) / ((p : ℚ) - 1) :=
    (le_div_iff₀ (sub_pos.mpr hp₁)).2 hq
  rw [factorialWeight, sub_mul, one_div, inv_mul_eq_div]
  exact sub_le_sub_left hbound _

/-- The set defining `B_p(t,r)` in the local sparse-polynomial root count has a greatest element. -/
theorem exists_greatest_factorialWeightIndex {p t : ℕ} [hp : Fact (Nat.Prime p)] {r : ℚ}
    (ht : 0 < t) (hr : 1 / ((p : ℚ) - 1) < r) :
    ∃ N, IsGreatest {k : ℕ | ∃ i : Fin t, factorialWeight p r k ≤ factorialWeight p r i} N := by
  let S : Set ℕ := {k | ∃ i : Fin t, factorialWeight p r k ≤ factorialWeight p r i}
  have hS : S.Nonempty := ⟨0, ⟨⟨0, ht⟩, le_rfl⟩⟩
  let δ : ℚ := r - 1 / ((p : ℚ) - 1)
  have hδ : 0 < δ := sub_pos.mpr hr
  have hp₁ : (1 : ℚ) < p := by exact_mod_cast hp.out.one_lt
  have hr₀ : 0 ≤ r := (one_div_pos.mpr (sub_pos.mpr hp₁)).le.trans hr.le
  obtain ⟨B, hB⟩ := exists_nat_gt (r * (t : ℚ) / δ)
  have hbounded : BddAbove S := by
    refine ⟨B, ?_⟩
    intro k hk
    obtain ⟨i, hi⟩ := hk
    have hit : ((i : ℕ) : ℚ) ≤ (t : ℚ) := by exact_mod_cast i.isLt.le
    have hiw : factorialWeight p r i ≤ r * (t : ℚ) :=
      (sub_le_self (r * ((i : ℕ) : ℚ)) (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_left hit hr₀)
    have hkw : δ * (k : ℚ) ≤ r * (t : ℚ) :=
      (factorialWeight_linear_le r k).trans (hi.trans hiw)
    have hkq : (k : ℚ) ≤ r * (t : ℚ) / δ :=
      (le_div_iff₀ hδ).2 (by simpa only [mul_comm] using hkw)
    exact_mod_cast (hkq.trans_lt hB).le
  exact hbounded.exists_isGreatest_of_nonempty hS

/-- Every index beyond the greatest admissible index has weight above all initial weights. -/
theorem factorialWeight_lt_of_gt_greatest {p t N k : ℕ} {r : ℚ}
    (hN : IsGreatest {n : ℕ | ∃ i : Fin t, factorialWeight p r n ≤ factorialWeight p r i} N)
    (hk : N < k) (i : Fin t) :
    factorialWeight p r i < factorialWeight p r k :=
  lt_of_not_ge fun hki ↦ (not_le_of_gt hk) (hN.2 ⟨i, hki⟩)

end GRHArticle.SingularModuli
