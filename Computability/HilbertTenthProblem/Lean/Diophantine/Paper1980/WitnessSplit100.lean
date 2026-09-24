import Diophantine.Paper1980.WitnessRoute100

/-!
# Splitting the counter values and the time equation of a canonical witness

`EXPLORATION_SERIAL_RAW_COUNTER_COMPOSITION.md`, §7: *"Use the ordinary ternary digit split of
each source counter value ... All counter, zero, and input slacks are positive."*

A value `v` is split into two Boolean words `lo + hi = v`: a digit `2` gives a `1` to both,
the lowest nonzero digit, if it is a `1`, goes to `hi`, and every other digit `1` goes to `lo`.
So `hi` is positive whenever `v` is, and `lo` is positive whenever `v` is even and positive,
because an even positive value is not a power of three.  The input block `2x` is even, so both
track words are positive.

`time_equation` is the counter note's factored time equation for a run: with
`A = Σ_b val_b R^b` and `κ⁺ − κ⁻ = Σ_b ε_b R^b`, the chains give `R³(A + κ⁺) + 2x = A + R³κ⁻`.
-/

namespace Jones1980

open Ternary Finset

/-- The position of the lowest nonzero digit (zero for zero). -/
noncomputable def lowPos (v : ℕ) : ℕ :=
  open Classical in if h : ∃ p, dg v p ≠ 0 then Nat.find h else 0

/-- The high half of the split. -/
noncomputable def splitHi (N v : ℕ) : ℕ :=
  val (fun i => if dg v i = 2 ∨ (dg v i = 1 ∧ i = lowPos v) then 1 else 0) N

/-- The low half of the split. -/
noncomputable def splitLo (N v : ℕ) : ℕ :=
  val (fun i => if dg v i = 2 ∨ (dg v i = 1 ∧ i ≠ lowPos v) then 1 else 0) N

theorem lowPos_spec {v : ℕ} (hv : v ≠ 0) : dg v (lowPos v) ≠ 0 := by
  have h : ∃ p, dg v p ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hv
    rw [← val_dg (Ternary.lt_three_pow v)]
    unfold Ternary.val
    exact Finset.sum_eq_zero fun p _ => by rw [hc p, zero_mul]
  unfold lowPos
  classical
  rw [dif_pos h]
  exact Nat.find_spec h

theorem splitHi_add_splitLo {N v : ℕ} (hv : v < 3 ^ N) : splitLo N v + splitHi N v = v := by
  unfold splitLo splitHi
  rw [val_add]
  conv_rhs => rw [← val_dg hv]
  congr 1
  funext i
  have := dg_le_two v i
  by_cases h2 : dg v i = 2
  · simp [h2]
  · by_cases h1 : dg v i = 1
    · by_cases hl : i = lowPos v
      · subst hl; simp [h1]
      · simp [h1, hl]
    · simp [h1, h2]; omega

theorem bool3_splitHi (N v : ℕ) : Bool3 (splitHi N v) := fun p => by
  unfold splitHi
  have hc : ∀ i, (if dg v i = 2 ∨ (dg v i = 1 ∧ i = lowPos v) then 1 else 0) ≤ 2 := fun i => by
    split_ifs <;> omega
  rcases Nat.lt_or_ge p N with hp | hp
  · rw [dg_val hc hp]; split_ifs <;> omega
  · rw [dg_val_of_ge hc hp]; omega

theorem bool3_splitLo (N v : ℕ) : Bool3 (splitLo N v) := fun p => by
  unfold splitLo
  have hc : ∀ i, (if dg v i = 2 ∨ (dg v i = 1 ∧ i ≠ lowPos v) then 1 else 0) ≤ 2 := fun i => by
    split_ifs <;> omega
  rcases Nat.lt_or_ge p N with hp | hp
  · rw [dg_val hc hp]; split_ifs <;> omega
  · rw [dg_val_of_ge hc hp]; omega

/-- A word with a nonzero digit at `p` is at least `3^p`. -/
theorem pow_le_of_dg_ne {X p : ℕ} (h : dg X p ≠ 0) : 3 ^ p ≤ X := by
  by_contra hc
  push_neg at hc
  exact h (dg_eq_zero_of_lt hc)

theorem splitHi_pos {N v : ℕ} (hv : v < 3 ^ N) (h0 : v ≠ 0) : 0 < splitHi N v := by
  have hs := lowPos_spec h0
  have hlt : lowPos v < N := by
    by_contra hc
    push_neg at hc
    exact hs (dg_eq_zero_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hc)))
  have hc : ∀ i, (if dg v i = 2 ∨ (dg v i = 1 ∧ i = lowPos v) then 1 else 0) ≤ 2 := fun i => by
    split_ifs <;> omega
  have hd : dg (splitHi N v) (lowPos v) = 1 := by
    unfold splitHi
    rw [dg_val hc hlt]
    have := dg_le_two v (lowPos v)
    rw [if_pos (by omega)]
  have := pow_le_of_dg_ne (show dg (splitHi N v) (lowPos v) ≠ 0 by omega)
  have : 0 < 3 ^ lowPos v := by positivity
  omega

theorem splitLo_pos {N v : ℕ} (hv : v < 3 ^ N) (h0 : v ≠ 0) (heven : 2 ∣ v) :
    0 < splitLo N v := by
  by_contra hz
  have hz0 : splitLo N v = 0 := by omega
  have hc : ∀ i, (if dg v i = 2 ∨ (dg v i = 1 ∧ i ≠ lowPos v) then 1 else 0) ≤ 2 := fun i => by
    split_ifs <;> omega
  have hdig : ∀ i, dg v i = if i = lowPos v then dg v (lowPos v) else 0 := by
    intro i
    rcases Nat.lt_or_ge i N with hi | hi
    · have h := dg_val hc hi
      unfold splitLo at hz0
      rw [hz0, dg_zero] at h
      have := dg_le_two v i
      by_cases hl : i = lowPos v
      · rw [if_pos hl, hl]
      · rw [if_neg hl]
        by_contra hne
        have hor : dg v i = 2 ∨ (dg v i = 1 ∧ i ≠ lowPos v) := by omega
        rw [if_pos hor] at h
        omega
    · rw [dg_eq_zero_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hi))]
      split_ifs with hl
      · rw [← hl, dg_eq_zero_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hi))]
      · rfl
  have hl1 : dg v (lowPos v) = 1 := by
    have h2 : dg v (lowPos v) ≠ 2 := by
      intro h2
      have hi : lowPos v < N := by
        by_contra hc'
        push_neg at hc'
        rw [dg_eq_zero_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) hc'))] at h2
        omega
      have h := dg_val hc hi
      unfold splitLo at hz0
      rw [hz0, dg_zero, if_pos (Or.inl h2)] at h
      omega
    have := lowPos_spec h0
    have := dg_le_two v (lowPos v)
    omega
  have hv3 : v = 3 ^ lowPos v := by
    have e1 : v = val (dg v) (v + 1) := (val_dg (Ternary.lt_three_pow _ |>.trans
      (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self v)))).symm
    have hle : lowPos v < v + 1 := by
      have := pow_le_of_dg_ne (lowPos_spec h0)
      have := Ternary.lt_three_pow (lowPos v)
      omega
    conv_lhs => rw [e1]
    unfold Ternary.val
    rw [Finset.sum_eq_single (lowPos v)]
    · rw [hl1, one_mul]
    · intro i _ hi
      rw [hdig i, if_neg hi, zero_mul]
    · intro h; exact absurd (Finset.mem_range.2 hle) h
  have := pow_three_mod_two (lowPos v)
  rw [← hv3] at this
  omega

/-- The split halves are digitwise below the repunit of any length the value fits in. -/
theorem dg_splitLo_le {N M v : ℕ} (hv : v < 3 ^ M) (p : ℕ) :
    dg (splitLo N v) p ≤ dg (rep M) p := by
  have hc : ∀ i, (if dg v i = 2 ∨ (dg v i = 1 ∧ i ≠ lowPos v) then 1 else 0) ≤ 2 := fun i => by
    split_ifs <;> omega
  rw [dg_rep]
  rcases Nat.lt_or_ge p N with hp | hp
  · unfold splitLo
    rw [dg_val hc hp]
    split_ifs with h1 h2 <;> try omega
    exfalso
    rw [dg_eq_zero_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h1
    omega
  · unfold splitLo
    rw [dg_val_of_ge hc hp]
    exact Nat.zero_le _

theorem dg_splitHi_le {N M v : ℕ} (hv : v < 3 ^ M) (p : ℕ) :
    dg (splitHi N v) p ≤ dg (rep M) p := by
  have hc : ∀ i, (if dg v i = 2 ∨ (dg v i = 1 ∧ i = lowPos v) then 1 else 0) ≤ 2 := fun i => by
    split_ifs <;> omega
  rw [dg_rep]
  rcases Nat.lt_or_ge p N with hp | hp
  · unfold splitHi
    rw [dg_val hc hp]
    split_ifs with h1 h2 <;> try omega
    exfalso
    rw [dg_eq_zero_of_lt (lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega)))] at h1
    omega
  · unfold splitHi
    rw [dg_val_of_ge hc hp]
    exact Nat.zero_le _

/-! ### The time equation of a run -/

/-- **The time equation.**  For a serial run with block radix `R`,
`R³(A + κ⁺) + 2x = A + R³κ⁻`, where `A`, `κ⁺`, `κ⁻` are the value and sign rows. -/
theorem Graph.time_equation {Gr : Graph} {x u : ℕ} {st val : ℕ → ℕ}
    (hR : Gr.SerialRun x u st val) (m : ℕ) :
    3 ^ (m * 3) * (rowsum val m u + rowsum (fun b => if Gr.sgn (st b) = true then 1 else 0) m u)
      + 2 * x = rowsum val m u
        + 3 ^ (m * 3) * rowsum (fun b => if Gr.sgn (st b) = true then 0 else 1) m u := by
  obtain ⟨h0, h1, h2⟩ := hR.init
  obtain ⟨f0, f1, f2⟩ := hR.final
  -- `Σ_{b<u+3} val_b R^b` two ways
  have hshift : ∀ n, rowsum val m (n + 3) = val 0 + 3 ^ m * val 1 + 3 ^ (m * 2) * val 2
      + 3 ^ (m * 3) * rowsum (fun b => val (b + 3)) m n := by
    intro n
    unfold rowsum
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ', Finset.mul_sum]
    simp only [Nat.mul_zero, pow_zero, Nat.mul_one]
    have e : ∀ i, val (i + 1 + 1 + 1) * 3 ^ (m * (i + 1 + 1 + 1))
        = 3 ^ (m * 3) * (val (i + 3) * 3 ^ (m * i)) := fun i => by
      rw [show i + 1 + 1 + 1 = i + 3 by ring, show m * (i + 3) = m * 3 + m * i by ring, pow_add]
      ring
    rw [Finset.sum_congr rfl fun i _ => e i]
    ring_nf
  have htop : rowsum val m (u + 3) = rowsum val m u := by
    rw [rowsum_succ, rowsum_succ, rowsum_succ, show u + 1 + 1 = u + 2 by ring, f0, f1, f2]
    ring
  have hchain : (rowsum (fun b => val (b + 3)) m u : ℤ) = rowsum val m u
      + rowsum (fun b => if Gr.sgn (st b) = true then 1 else 0) m u
      - rowsum (fun b => if Gr.sgn (st b) = true then 0 else 1) m u := by
    unfold rowsum
    push_cast
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hu := hR.update b (Finset.mem_range.1 hb)
    rw [hu]
    split_ifs <;> push_cast <;> ring
  have hs := hshift u
  rw [htop, h0, h1, h2] at hs
  have hsZ : (rowsum val m u : ℤ) = 2 * x + 3 ^ (m * 3) * rowsum (fun b => val (b + 3)) m u := by
    exact_mod_cast (by rw [hs]; ring : rowsum val m u = 2 * x + 3 ^ (m * 3) *
      rowsum (fun b => val (b + 3)) m u)
  rw [hchain] at hsZ
  have : ((3 ^ (m * 3) * (rowsum val m u + rowsum (fun b => if Gr.sgn (st b) = true then 1 else 0)
      m u) + 2 * x : ℕ) : ℤ) = ((rowsum val m u + 3 ^ (m * 3) *
      rowsum (fun b => if Gr.sgn (st b) = true then 0 else 1) m u : ℕ) : ℤ) := by
    push_cast
    linarith
  exact_mod_cast this

end Jones1980
