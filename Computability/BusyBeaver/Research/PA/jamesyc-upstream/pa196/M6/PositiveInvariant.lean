module
public import M6.Zip

@[expose] public section

namespace M6.Zip

/-- An invariant with a strictly positive finite continuation at each invariant
configuration excludes any finite halt. Intermediate configurations need not
satisfy the invariant, so macro-step simulations can use this theorem directly.
Zero-step stuttering would not suffice. -/
theorem not_halts_of_positive_invariant (M : TMN) (Inv : Conf → Prop)
    (progress : ∀ c, Inv c → ∃ d, Reach1 M c d ∧ Inv d)
    (c₀ : Conf) (initial : Inv c₀) : ¬ Halts M c₀ := by
  rintro ⟨terminal, ⟨n, hrun⟩, hstop⟩
  have impossible : ∀ n c, Inv c → run M n c = some terminal → False := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        intro c hc hr
        obtain ⟨d, ⟨k, hmove⟩, hd⟩ := progress c hc
        by_cases hkn : k < n
        · have hle : k + 1 ≤ n := by omega
          obtain ⟨remaining, heq⟩ := Nat.exists_eq_add_of_le hle
          have htail : run M remaining d = some terminal := by
            rw [heq, run_add, hmove] at hr
            exact hr
          exact ih remaining (by omega) d hd htail
        · have hle : n ≤ k := by omega
          obtain ⟨remaining, heq⟩ := Nat.exists_eq_add_of_le hle
          have hlong : run M (n + (remaining + 1)) c = some d := by
            simpa only [heq, Nat.add_assoc] using hmove
          rw [run_add, hr] at hlong
          simp only [run, hstop] at hlong
          cases hlong
  exact impossible n c₀ initial hrun

end M6.Zip
