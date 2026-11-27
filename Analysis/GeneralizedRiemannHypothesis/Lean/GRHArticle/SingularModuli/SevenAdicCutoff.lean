import GRHArticle.SingularModuli.FactorialThreshold

/-!
# Factorial weights for the depth-half 7-adic disk

The weights w_{p,r}(k) = rk - v_p(k!) are those in smd:lem:disk in
Analysis/GeneralizedRiemannHypothesis/Article/sections/smd.tex.
The calculation below gives the bound B₇(3, 1/2) = 2 used in the trinomial case.
-/

namespace GRHArticle.SingularModuli

theorem one_lt_seven_half_weight {k : ℕ} (hk : 3 ≤ k) :
    1 < factorialWeight 7 (1 / 2) k := by
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h : 6 * padicValNat 7 k.factorial < k :=
    sub_one_mul_padicValNat_factorial_lt_of_ne_zero 7 (by omega)
  have hq : (6 : ℚ) * (padicValNat 7 k.factorial : ℚ) < (k : ℚ) := by exact_mod_cast h
  have hkq : (3 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
  unfold factorialWeight
  linarith

theorem seven_half_weight_le_one_iff (k : ℕ) :
    factorialWeight 7 (1 / 2) k ≤ 1 ↔ k ≤ 2 := by
  constructor
  · intro h
    by_contra! hk
    exact (not_le_of_gt (one_lt_seven_half_weight (by omega))) h
  · intro hk
    have hkq : (k : ℚ) ≤ 2 := by exact_mod_cast hk
    have hn : (0 : ℚ) ≤ (padicValNat 7 k.factorial : ℚ) := by positivity
    unfold factorialWeight
    linarith

theorem seven_half_weight_two : factorialWeight 7 (1 / 2) 2 = 1 := by
  have h : padicValNat 7 (Nat.factorial 2) = 0 :=
    padicValNat.eq_zero_of_not_dvd (by decide)
  norm_num [factorialWeight, h]

/-- The greatest index whose weight is at most some initial weight is 2,
the exact value of the article's B₇(3, 1/2). -/
theorem seven_half_trinomial_cutoff :
    IsGreatest {k : ℕ | ∃ i < 3, factorialWeight 7 (1 / 2) k ≤
      factorialWeight 7 (1 / 2) i} 2 := by
  refine ⟨⟨2, by decide, le_rfl⟩, ?_⟩
  intro k hk
  obtain ⟨i, hi, hki⟩ := hk
  apply (seven_half_weight_le_one_iff k).mp
  exact hki.trans ((seven_half_weight_le_one_iff i).mpr (by omega))

end GRHArticle.SingularModuli
