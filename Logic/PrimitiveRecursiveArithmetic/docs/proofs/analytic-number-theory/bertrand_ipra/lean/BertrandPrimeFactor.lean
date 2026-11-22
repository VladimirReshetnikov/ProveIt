import BertrandSearch

namespace Bertrand

/-- A failed bounded trial-division scan returns an offending trial divisor. -/
theorem passes_failure (n k : Nat) (h : passes n k = false) :
    ∃ d, 2 ≤ d ∧ d ≤ k ∧ d ∣ n := by
  induction k with
  | zero => simp [passes] at h
  | succ k ih =>
    by_cases old : passes n k = false
    · obtain ⟨d, hd, hk, hh⟩ := ih old
      exact ⟨d, hd, by omega, hh⟩
    · have good : passes n k = true := by cases he : passes n k <;> simp_all
      have hd : 2 ≤ k+1 := by
        by_cases hl : k+1 < 2
        · simp [passes, good, hl] at h
        · omega
      have hm : n % (k+1) = 0 := by
        by_cases hz : n % (k+1) = 0
        · exact hz
        · simp [passes, good, hz] at h
      exact ⟨k+1, hd, Nat.le_refl _, Nat.dvd_of_mod_eq_zero hm⟩

theorem exists_prime_factor {n : Nat} (hn : 2 ≤ n) : ∃ p, Prime p ∧ p ∣ n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hb : primeB n = true
    · exact ⟨n, (primeB_spec _).mp hb, Nat.dvd_refl n⟩
    · have hf : passes n (n-1) = false := by
        by_cases h : passes n (n-1) = true
        · exact False.elim (hb (by simp [primeB,hn,h]))
        · cases he : passes n (n-1) <;> simp_all
      obtain ⟨d, hd, hk, hh⟩ := passes_failure n (n-1) hf
      obtain ⟨p, hp, hv⟩ := ih d (by omega) hd
      exact ⟨p, hp, Nat.dvd_trans hv hh⟩

end Bertrand
