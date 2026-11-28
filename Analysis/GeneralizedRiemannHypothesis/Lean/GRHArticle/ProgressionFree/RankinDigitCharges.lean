import GRHArticle.ProgressionFree.RankinDigitSplit

/-!
# Ternary witness charges

Mark the positions of digit two with digit one. The resulting greedy mask
gives the step from either of the two greedy predecessors. The mask has a
nonzero high part exactly at the cuts where the original high part is bad.
-/

namespace GRHArticle.ProgressionFree

private theorem mem_greedyExponents_add_three_mul {t n : ℕ} (ht : t ≤ 1)
    (hn : n ∈ greedyExponents) : t+3*n ∈ greedyExponents :=
  (mem_greedyExponents_add_pow_mul_iff t n 1 (by norm_num; omega)).mpr
    ⟨(mem_greedyExponents_iff t).mpr ⟨by omega,
      (show t/3 = 0 by omega).symm ▸ zero_mem_greedyExponents⟩,hn⟩

/-- The two greedy predecessors have a step whose digits record every
occurrence of digit two, including whether any occurrence lies above a cut. -/
theorem exists_greedy_digitCharge (n : ℕ) :
    ∃ a d : ℕ, a+2*d = n ∧ a ∈ greedyExponents ∧ a+d ∈ greedyExponents ∧ d ∈ greedyExponents ∧
      ∀ k : ℕ, (n/3^k ∉ greedyExponents ↔ 0 < d/3^k) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h₀ : n = 0
    · subst n
      refine ⟨0,0,rfl,zero_mem_greedyExponents,zero_mem_greedyExponents,zero_mem_greedyExponents,?_⟩
      intro k
      simp [zero_mem_greedyExponents]
    · obtain ⟨a,d,he,ha,hab,hd,hHigh⟩ := ih (n/3)
        (Nat.div_lt_self (Nat.pos_of_ne_zero h₀) (by decide))
      let r := n%3
      let t := if r = 2 then 0 else r
      let e := if r = 2 then 1 else 0
      have ht : t ≤ 1 := by dsimp [t,r]; split <;> omega
      have he₁ : e ≤ 1 := by dsimp [e]; split <;> omega
      have ht₁ : t+e ≤ 1 := by
        by_cases hr : r = 2
        · simp [t,e,hr]
        · have hR : r ≤ 1 := by dsimp [r] at hr ⊢; omega
          simpa only [t,e,if_neg hr,add_zero] using hR
      have hDigit : t+2*e = n%3 := by dsimp [t,e,r]; split <;> simp_all
      have hEq : (t+3*a)+2*(e+3*d) = n := by
        have := Nat.mod_add_div n 3
        omega
      have hGood : (t+3*a)+(e+3*d) ∈ greedyExponents := by
        rw [show (t+3*a)+(e+3*d) = (t+e)+3*(a+d) by omega]
        exact mem_greedyExponents_add_three_mul ht₁ hab
      refine ⟨t+3*a,e+3*d,hEq,mem_greedyExponents_add_three_mul ht ha,hGood,
        mem_greedyExponents_add_three_mul he₁ hd,?_⟩
      intro k
      cases k with
      | zero =>
        simp only [pow_zero,Nat.div_one]
        rw [mem_greedyExponents_iff n,not_and_or]
        have h := hHigh 0
        simp only [pow_zero,Nat.div_one] at h
        rw [h]
        by_cases hr : n%3 = 2
        · simp [e,r,hr]
        · have hR : n%3 ≤ 1 := by omega
          simp only [hR,not_true_eq_false,false_or,e,r,if_neg hr,zero_add]
          omega
      | succ k =>
        rw [pow_succ',← Nat.div_div_eq_div_mul,← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (by decide),Nat.div_eq_of_lt (by omega : e < 3),zero_add]
        exact hHigh k

end GRHArticle.ProgressionFree
