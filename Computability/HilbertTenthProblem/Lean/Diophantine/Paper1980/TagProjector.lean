import Diophantine.Paper1980.TagRows

/-!
# The row projector: `2Q + S = M` with Boolean words

`EXPLORATION_SINGLE_CONTENT_GUARD_TAG.md`, §4, and `EXPLORATION_REORDERED_STARTUP_TAG.md`, §3.
For Boolean ternary words `Q, S, M` with `2Q + S = M`, the carry automaton of the sum
forces: the carry into position `p + 1` is the digit of `Q` at `p`; a `1` of `Q` is either
at a `1` of `S` or continues a run from below; a run never reaches a `1` of `S`.

In the row setting (`R = 3^m`, heads at the positions `m·i`, `i < t`), with `S ⊆ heads`
and the `α`-offset of every row free in `Q` (from the Boolean guard `G = Q + 3^α·heads`),
every `1` of `Q` belongs to a run that starts at the head of its row (which carries a `1`
of `S`) and stays strictly below the offset `α`.  Consequently row `i` of `Q` is `rep ℓᵢ`
and row `i` of `M` is the single marker `3^ℓᵢ`, `ℓᵢ ≤ α`, when the head selector `sᵢ` is
`1`, and both rows vanish when `sᵢ = 0`.

The file also provides the digits of the shifted head words `3^α · heads m t` and
`rep b · heads m t` (`b < m`).
-/

namespace Jones1980

namespace Ternary

/-! ### Shifted head words -/

theorem dg_pow_mul_heads {m α : ℕ} (hm : 1 ≤ m) (hα : α < m) (t p : ℕ) :
    dg (3 ^ α * heads m t) p = if p % m = α ∧ p < m * t then 1 else 0 := by
  rcases Nat.lt_or_ge p α with hp | hp
  · rw [dg_mul_pow_of_lt _ hp]
    have : p % m ≠ α := by rw [Nat.mod_eq_of_lt (by omega)]; omega
    simp [this]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
    rw [dg_mul_pow_add, dg_heads hm]
    by_cases hk : k % m = 0 ∧ k < m * t
    · obtain ⟨hk1, hk2⟩ := hk
      have h1 : (α + k) % m = α := by
        rw [Nat.add_mod, hk1, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hα]
      have h2 : α + k < m * t := by
        obtain ⟨c, hc⟩ : ∃ c, k = m * c := ⟨k / m, by have := Nat.div_add_mod k m; omega⟩
        subst hc
        have : c < t := by
          by_contra h; push Not at h
          have : m * t ≤ m * c := Nat.mul_le_mul_left _ h
          omega
        have : c + 1 ≤ t := this
        calc α + m * c < m + m * c := by omega
          _ = m * (c + 1) := by ring
          _ ≤ m * t := Nat.mul_le_mul_left _ this
      simp [hk1, hk2, h1, h2]
    · have : ¬((α + k) % m = α ∧ α + k < m * t) := by
        intro ⟨h1, h2⟩
        apply hk
        refine ⟨?_, by omega⟩
        have h3 : (α + k) % m = (α + k % m) % m := by rw [Nat.add_mod, Nat.mod_eq_of_lt hα]
        rw [h3] at h1
        have h4 : k % m < m := Nat.mod_lt _ (by omega)
        rcases Nat.lt_or_ge (α + k % m) m with h5 | h5
        · rw [Nat.mod_eq_of_lt h5] at h1; omega
        · have h6 : (α + k % m) % m = α + k % m - m := by
            rw [Nat.mod_eq_sub_mod h5, Nat.mod_eq_of_lt (by omega)]
          omega
      simp [hk, this]

theorem bool3_pow_mul_heads {m α : ℕ} (hm : 1 ≤ m) (hα : α < m) (t : ℕ) :
    Bool3 (3 ^ α * heads m t) := (bool3_heads hm t).mul_pow α

/-- The digits of `rep b · heads m t` for `b < m`: a `1` at the offsets below `b` of every
row below `t`. -/
theorem dg_rep_mul_heads {m : ℕ} (hm : 1 ≤ m) (t : ℕ) :
    ∀ b, b < m → ∀ p, dg (rep b * heads m t) p = if p % m < b ∧ p < m * t then 1 else 0
  | 0, _, p => by simp [rep_zero]
  | b + 1, hb, p => by
    have ih := dg_rep_mul_heads hm t b (by omega)
    rw [rep_succ, add_mul, dg_add_of_le_two]
    · rw [ih, dg_pow_mul_heads hm (by omega)]
      have hpm : p % m < m := Nat.mod_lt _ (by omega)
      split_ifs <;> omega
    · intro p'
      rw [ih, dg_pow_mul_heads hm (by omega)]
      split_ifs <;> omega

/-! ### The carry automaton of `2Q + S` -/

section Automaton

variable {Q S : ℕ} (hQ : Bool3 Q) (hS : Bool3 S) (hM : Bool3 (2 * Q + S))

include hQ hS

theorem carry_two_le_one : ∀ p, carry 2 1 Q S p ≤ 1
  | 0 => by simp
  | p + 1 => by
    rw [carry_succ]
    have := hQ p; have := hS p; have := carry_two_le_one p
    omega

include hM

theorem dg_two_mul_add (p : ℕ) :
    dg (2 * Q + S) p = (2 * dg Q p + dg S p + carry 2 1 Q S p) % 3 := by
  have := dg_lin 2 1 Q S p
  rw [one_mul, one_mul] at this
  exact this

/-- The carry into `p + 1` is the digit of `Q` at `p`. -/
theorem carry_two_succ (p : ℕ) : carry 2 1 Q S (p + 1) = dg Q p := by
  have hm := hM p
  rw [dg_two_mul_add hQ hS hM] at hm
  rw [carry_succ, one_mul]
  have h1 := hQ p; have h2 := hS p; have h3 := carry_two_le_one hQ hS p
  generalize dg Q p = a at *
  generalize dg S p = b at *
  generalize carry 2 1 Q S p = c at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> omega

/-- A `1` of `Q` is at a `1` of `S` or continues a run (incoming carry). -/
theorem q_one_imp {p : ℕ} (h : dg Q p = 1) : dg S p = 1 ∨ carry 2 1 Q S p = 1 := by
  have hm := hM p
  rw [dg_two_mul_add hQ hS hM] at hm
  have h2 := hS p; have h3 := carry_two_le_one hQ hS p
  rw [h] at hm
  generalize dg S p = b at *
  generalize carry 2 1 Q S p = c at *
  interval_cases b <;> interval_cases c <;> omega

end Automaton

/-- With every head of `Q` free (the case `A = 1`), `Q` vanishes: a `1` inside a row would
continue a run from below, down to a head. -/
theorem Q_eq_zero_of_heads_free {Q S m t : ℕ} (hm : 1 ≤ m) (hQ : Bool3 Q) (hS : Bool3 S)
    (hM : Bool3 (2 * Q + S)) (hSH : ∀ p, dg S p = 1 → p % m = 0 ∧ p < m * t)
    (hQ0 : ∀ i, i < t → dg Q (m * i) = 0) (hQlt : Q < 3 ^ (m * t)) : Q = 0 := by
  have hall : ∀ p, dg Q p = 0 := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
      by_contra h
      have h1 : dg Q p = 1 := by have := hQ p; omega
      have hpt : p < m * t := by
        by_contra hge; push Not at hge
        have : dg Q p = 0 :=
          dg_eq_zero_of_lt (lt_of_lt_of_le hQlt (Nat.pow_le_pow_right (by norm_num) hge))
        omega
      rcases Nat.eq_zero_or_pos (p % m) with hk | hk
      · have hi : p / m < t := by
          rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith [Nat.mul_comm m t]
        have := hQ0 (p / m) hi
        have e : m * (p / m) = p := by have := Nat.div_add_mod p m; omega
        rw [e] at this; omega
      · have hS0 : dg S p ≠ 1 := by
          intro hs
          have h2 := (hSH p hs).1
          omega
        rcases q_one_imp hQ hS hM h1 with hs | hc
        · exact hS0 hs
        · have hp0 : 0 < p := Nat.pos_of_ne_zero (fun h0 => by subst h0; simp at hk)
          obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
          rw [carry_two_succ hQ hS hM] at hc
          have := ih p' (by omega)
          omega
  have : Q = val (dg Q) (m * t) := (val_dg hQlt).symm
  rw [this]
  unfold val
  exact Finset.sum_eq_zero fun p _ => by rw [hall p]; ring

/-! ### The run structure in rows -/

/-- A row is determined by its digits. -/
theorem row_eq_of_dg {X Y m i : ℕ} (hY : Y < 3 ^ m)
    (h : ∀ k, k < m → dg X (m * i + k) = dg Y k) : row X m i = Y := by
  have h1 : ∀ k, dg (row X m i) k = dg Y k := by
    intro k
    rcases Nat.lt_or_ge k m with hk | hk
    · rw [dg_row _ _ hk, h k hk]
    · rw [dg_row_of_ge _ _ hk,
        dg_eq_zero_of_lt (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) hk))]
  have h2 : row X m i < 3 ^ m := row_lt _ _ _
  rw [← val_dg h2, ← val_dg hY]
  unfold val
  exact Finset.sum_congr rfl fun p _ => by rw [h1 p]

section Rows

variable {Q S m t α : ℕ} (hm : 1 ≤ m) (hα : 1 ≤ α) (hαm : α < m)
  (hQ : Bool3 Q) (hS : Bool3 S) (hM : Bool3 (2 * Q + S))
  (hSH : ∀ p, dg S p = 1 → p % m = 0 ∧ p < m * t)
  (hQα : ∀ i, i < t → dg Q (m * i + α) = 0) (hQlt : Q < 3 ^ (m * t))

include hm hα hαm hQ hS hM hSH hQα hQlt

omit hα hαm hS hM hSH hQα in
/-- A `1` of `Q` lies below `m·t`, so its row index is below `t`. -/
theorem row_lt_of_dg_one {i k : ℕ} (h : dg Q (m * i + k) = 1) : i < t := by
  by_contra hit
  push Not at hit
  have h1 : m * t ≤ m * i := Nat.mul_le_mul_left _ hit
  have h2 : dg Q (m * i + k) = 0 :=
    dg_eq_zero_of_lt (lt_of_lt_of_le hQlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
  omega

omit hm hα hαm hQ hM hQα hQlt in
/-- A `1` of `S` inside a row is at its head. -/
theorem dg_S_eq_zero_of_offset {i k : ℕ} (hk : 0 < k) (hkm : k < m) : dg S (m * i + k) = 0 := by
  by_contra h
  have h1 : dg S (m * i + k) = 1 := by have := hS (m * i + k); omega
  have h2 := (hSH _ h1).1
  rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hkm] at h2
  omega

/-- Every `1` of `Q` belongs to a run from the head of its row, whose head carries a `1` of
`S`, and lies strictly below the offset `α`. -/
theorem run_structure : ∀ i k, k < m → dg Q (m * i + k) = 1 →
    (∀ k', k' ≤ k → dg Q (m * i + k') = 1) ∧ dg S (m * i) = 1 ∧ k < α := by
  intro i
  induction i with
  | zero =>
    intro k
    induction k with
    | zero =>
      intro _ hp
      simp only [mul_zero, zero_add] at hp ⊢
      refine ⟨fun k' hk' => by rw [Nat.le_zero.1 hk']; exact hp, ?_, hα⟩
      rcases q_one_imp hQ hS hM hp with h | h
      · exact h
      · simp at h
    | succ k ihk =>
      intro hk hp
      simp only [mul_zero, zero_add] at hp ihk ⊢
      have hSk : dg S (k + 1) = 0 := by
        have := dg_S_eq_zero_of_offset hS hSH (i := 0) (k := k + 1) (by omega) hk
        simpa using this
      have hc : carry 2 1 Q S (k + 1) = 1 := by
        rcases q_one_imp hQ hS hM hp with h | h
        · omega
        · exact h
      rw [carry_two_succ hQ hS hM] at hc
      obtain ⟨hrun, hhead, hlt⟩ := ihk (by omega) hc
      have hit : 0 < t := row_lt_of_dg_one hm hQ hQlt (i := 0) (k := k + 1) (by simpa using hp)
      refine ⟨fun k' hk' => ?_, hhead, ?_⟩
      · rcases Nat.lt_or_ge k' (k + 1) with h | h
        · exact hrun k' (by omega)
        · rw [show k' = k + 1 by omega]; exact hp
      · have h0 := hQα 0 hit
        simp only [mul_zero, zero_add] at h0
        by_contra h
        have : k + 1 = α := by omega
        rw [this] at hp; omega
  | succ i ihi =>
    intro k
    induction k with
    | zero =>
      intro _ hp
      rw [add_zero] at hp
      refine ⟨fun k' hk' => by rw [Nat.le_zero.1 hk', add_zero]; exact hp, ?_, hα⟩
      rcases q_one_imp hQ hS hM hp with h | h
      · exact h
      · exfalso
        have e : m * (i + 1) = m * i + (m - 1) + 1 := by rw [Nat.mul_succ]; omega
        rw [e, carry_two_succ hQ hS hM] at h
        have := (ihi (m - 1) (by omega) h).2.2
        omega
    | succ k ihk =>
      intro hk hp
      have hSk : dg S (m * (i + 1) + (k + 1)) = 0 :=
        dg_S_eq_zero_of_offset hS hSH (by omega) hk
      have hc : carry 2 1 Q S (m * (i + 1) + (k + 1)) = 1 := by
        rcases q_one_imp hQ hS hM hp with h | h
        · omega
        · exact h
      rw [← add_assoc, carry_two_succ hQ hS hM] at hc
      obtain ⟨hrun, hhead, hlt⟩ := ihk (by omega) hc
      have hit : i + 1 < t := row_lt_of_dg_one hm hQ hQlt hp
      refine ⟨fun k' hk' => ?_, hhead, ?_⟩
      · rcases Nat.lt_or_ge k' (k + 1) with h | h
        · exact hrun k' (by omega)
        · rw [show k' = k + 1 by omega]; exact hp
      · have h0 := hQα (i + 1) hit
        by_contra h
        have : k + 1 = α := by omega
        rw [this] at hp; omega

/-- The digit of `Q` at the offset `k` of a row is zero unless `k < α`. -/
theorem dg_Q_offset_ge {i k : ℕ} (hkm : k < m) (hk : α ≤ k) : dg Q (m * i + k) = 0 := by
  by_contra h
  have h1 : dg Q (m * i + k) = 1 := by have := hQ (m * i + k); omega
  have := (run_structure hm hα hαm hQ hS hM hSH hQα hQlt i k hkm h1).2.2
  omega

/-- The carry into the head of every row vanishes. -/
theorem carry_head (i : ℕ) : carry 2 1 Q S (m * i) = 0 := by
  rcases Nat.eq_zero_or_pos i with h0 | h0
  · subst h0; simp
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have e : m * (i' + 1) = m * i' + (m - 1) + 1 := by rw [Nat.mul_succ]; omega
    rw [e, carry_two_succ hQ hS hM]
    exact dg_Q_offset_ge hm hα hαm hQ hS hM hSH hQα hQlt (by omega) (by omega)

/-- The rows of `Q` and `M = 2Q + S` below `t`: with the head selector `sᵢ = dg S (m i)`,
row `i` of `Q` is `rep ℓᵢ` and row `i` of `M` is `3^ℓᵢ` (`ℓᵢ ≤ α`) when `sᵢ = 1`, and both
vanish when `sᵢ = 0`. -/
theorem rows_of_projector {i : ℕ} (hi : i < t) :
    ∃ ℓ, ℓ ≤ α ∧
      row Q m i = (if dg S (m * i) = 1 then rep ℓ else 0) ∧
      row (2 * Q + S) m i = (if dg S (m * i) = 1 then 3 ^ ℓ else 0) := by
  have hex : ∃ k, dg Q (m * i + k) = 0 := ⟨α, hQα i hi⟩
  classical
  obtain ⟨ℓ, hℓ0, hℓmin⟩ : ∃ ℓ, dg Q (m * i + ℓ) = 0 ∧ ∀ k, k < ℓ → dg Q (m * i + k) ≠ 0 :=
    ⟨Nat.find hex, Nat.find_spec hex, fun k hk => Nat.find_min hex hk⟩
  have hℓα : ℓ ≤ α := by
    by_contra h
    exact hℓmin α (by omega) (hQα i hi)
  have hrun : ∀ k, k < ℓ → dg Q (m * i + k) = 1 := by
    intro k hk
    have := hℓmin k hk
    have := hQ (m * i + k)
    omega
  have hzero : ∀ k, ℓ ≤ k → k < m → dg Q (m * i + k) = 0 := by
    intro k hk hkm
    by_contra h
    have h1 : dg Q (m * i + k) = 1 := by have := hQ (m * i + k); omega
    have := (run_structure hm hα hαm hQ hS hM hSH hQα hQlt i k hkm h1).1 ℓ hk
    omega
  have hs_or : dg S (m * i) = 1 ∨ ℓ = 0 := by
    by_contra h
    push Not at h
    have h1 := hrun 0 (by omega)
    rw [add_zero] at h1
    have := (run_structure hm hα hαm hQ hS hM hSH hQα hQlt i 0 (by omega)
      (by rw [add_zero]; exact h1)).2.1
    exact h.1 this
  refine ⟨ℓ, hℓα, ?_, ?_⟩
  · -- the row of `Q`
    apply row_eq_of_dg
    · split_ifs
      · exact lt_of_lt_of_le (rep_lt ℓ) (Nat.pow_le_pow_right (by norm_num) (by omega))
      · positivity
    · intro k hk
      by_cases hs : dg S (m * i) = 1
      · rw [if_pos hs, dg_rep]
        rcases Nat.lt_or_ge k ℓ with h | h
        · rw [hrun k h, if_pos h]
        · rw [hzero k h hk, if_neg (by omega)]
      · rw [if_neg hs, dg_zero]
        have hℓ : ℓ = 0 := hs_or.resolve_left hs
        exact hzero k (by omega) hk
  · -- the row of `M`
    apply row_eq_of_dg
    · split_ifs
      · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      · positivity
    · intro k hk
      rw [dg_two_mul_add hQ hS hM]
      have hc : carry 2 1 Q S (m * i + k) = if k = 0 then 0 else dg Q (m * i + (k - 1)) := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; rw [add_zero, if_pos rfl]; exact carry_head hm hα hαm hQ hS hM hSH hQα hQlt i
        · rw [if_neg (by omega), show m * i + k = m * i + (k - 1) + 1 by omega,
            carry_two_succ hQ hS hM]
      have hSk : dg S (m * i + k) = if k = 0 then dg S (m * i) else 0 := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp
        · rw [if_neg (by omega)]; exact dg_S_eq_zero_of_offset hS hSH h0 hk
      have hQk : dg Q (m * i + k) = if k < ℓ then 1 else 0 := by
        split_ifs with h
        · exact hrun k h
        · exact hzero k (by omega) hk
      have hQk' : 0 < k → dg Q (m * i + (k - 1)) = if k - 1 < ℓ then 1 else 0 := by
        intro h0
        split_ifs with h
        · exact hrun _ h
        · exact hzero _ (by omega) (by omega)
      by_cases hs : dg S (m * i) = 1
      · rw [if_pos hs, dg_pow, hc, hSk, hQk]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0
          rcases Nat.eq_zero_or_pos ℓ with hl | hl
          · subst hl; simp [hs]
          · have hl' : ¬ (0 = ℓ) := fun h => by omega
            simp [hs, hl, hl']
        · have hk0 : ¬ k = 0 := by omega
          rw [hQk' h0, if_neg hk0, if_neg hk0]
          rcases lt_trichotomy k ℓ with h1 | h1 | h1
          · simp only [if_pos h1, if_pos (show k - 1 < ℓ by omega), if_neg (show ¬ k = ℓ by omega)]
          · subst h1
            simp [h0]
          · simp only [if_neg (show ¬ k < ℓ by omega), if_neg (show ¬ k - 1 < ℓ by omega),
              if_neg (show ¬ k = ℓ by omega)]
      · rw [if_neg hs, dg_zero]
        have hs0 : dg S (m * i) = 0 := by have := hS (m * i); omega
        have hℓ : ℓ = 0 := hs_or.resolve_left hs
        subst hℓ
        rw [hc, hSk, hQk]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp [hs0]
        · rw [hQk' h0]
          simp [Nat.pos_iff_ne_zero.1 h0]

end Rows

end Ternary

end Jones1980
