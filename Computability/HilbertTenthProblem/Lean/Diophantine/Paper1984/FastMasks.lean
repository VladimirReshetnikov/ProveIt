import Diophantine.Paper1984.Blocks
import Diophantine.Paper1984.Identities

/-!
# Jones–Matijasevič 1984, §4: the masking conditions for the fast commands

For `Q = 2^q` and block histories `R_j = Σ r_t Q^t`, `L = Σ l_t Q^t` (`l_t ∈ {0, 1}`),
`I = Σ Q^t`:

* (47) ⟺ (48): `M ≼ R_j`, `M ≼ (Q − 1)L`, `R_j ≼ (Q − 1)(I − L) + M` hold exactly for
  `M = Σ r_t l_t Q^t` (the addition command `R_i ← R_i + R_j`);
* (49) ⟺ (50): `2J ≼ R_j`, `J ≼ (Q/2 − 1)L`, `R_j ≼ (Q − 1)(I − L) + 2J + L` hold exactly for
  `J = Σ ⌊r_t/2⌋ l_t Q^t` (the halving command), with the corrected final term `L`;
* (52): for one-hot line histories, `QL_n ≼ L_i + L_j` (`i ≠ j`) says that every step from
  line `n` goes to line `i` or line `j`;
* (43): `R ≡ 0 (mod 2) ⟺ 2⌈R/2⌉ ≤ R`.
-/

namespace JM1984

theorem Mask.antisymm {a b : ℕ} (h1 : a ≼ b) (h2 : b ≼ a) : a = b :=
  Nat.eq_of_testBit_eq fun i => by
    cases ha : a.testBit i <;> cases hb : b.testBit i
    · rfl
    · exact absurd (h2 i hb) (by simp [ha])
    · exact absurd (h1 i ha) (by simp [hb])
    · rfl

/-- A number masked by a block number of proper blocks is itself a block number. -/
theorem blocks_of_mask {q n : ℕ} {g : ℕ → ℕ} (hg : ∀ t < n, g t < 2 ^ q) {M : ℕ}
    (h : M ≼ blocks (2 ^ q) n g) : M = blocks (2 ^ q) n (digit (2 ^ q) M) :=
  (blocks_digit (by positivity) (lt_of_le_of_lt h.le (blocks_lt hg))).symm

/-- The identity (43). -/
theorem even_iff_two_mul_ceil (R : ℕ) : R % 2 = 0 ↔ 2 * ((R + 1) / 2) ≤ R := by omega

/-- A number between `2j` and `2j + 1` in the masking order has quotient `j`. -/
theorem div_two_of_masks {j r : ℕ} (h1 : 2 * j ≼ r) (h2 : r ≼ 2 * j + 1) : r / 2 = j := by
  have a := ((mask_iff_div2 _ _).1 h1).2
  have b := ((mask_iff_div2 _ _).1 h2).2
  rw [show 2 * j / 2 = j by omega] at a
  rw [show (2 * j + 1) / 2 = j by omega] at b
  exact Mask.antisymm b a

section

variable {q n : ℕ} {r l : ℕ → ℕ}

local notation "Q" => 2 ^ q

/-- **(47) ⟺ (48).** -/
theorem mask47_iff (hr : ∀ t < n, r t < Q) (hl : ∀ t < n, l t ≤ 1) (M : ℕ) :
    (M ≼ blocks Q n r ∧ M ≼ (Q - 1) * blocks Q n l ∧
      blocks Q n r ≼ (Q - 1) * (blocks Q n (fun _ => 1) - blocks Q n l) + M) ↔
      M = blocks Q n (fun t => r t * l t) := by
  have hQ : 0 < Q := by positivity
  have hL : (Q - 1) * blocks Q n l = blocks Q n (fun t => (Q - 1) * l t) :=
    (blocks_smul _ _ _ _).symm
  have hLlt : ∀ t < n, (Q - 1) * l t < Q := fun t ht => by
    have := hl t ht
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 this with h | h <;> rw [h] <;> omega
  have hIL : ∀ m : ℕ → ℕ, (Q - 1) * (blocks Q n (fun _ => 1) - blocks Q n l) + blocks Q n m =
      blocks Q n (fun t => (Q - 1) * (1 - l t) + m t) := by
    intro m
    rw [← blocks_sub (fun t ht => hl t ht), ← blocks_smul, ← blocks_add]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hL] at h2
    have hM := blocks_of_mask hLlt h2
    set m := digit Q M with hm
    have hmQ : ∀ t < n, m t < Q := fun t _ => digit_lt hQ _ _
    rw [hM] at h1 h2 h3
    have h1' := (mask_blocks_iff hmQ hr).1 h1
    have h2' := (mask_blocks_iff hmQ hLlt).1 h2
    have hm0 : ∀ t < n, l t = 0 → m t = 0 := fun t ht hl0 => by
      have := h2' t ht
      rw [hl0, mul_zero, mask_zero_iff] at this
      exact this
    rw [hIL] at h3
    have hgQ : ∀ t < n, (Q - 1) * (1 - l t) + m t < Q := fun t ht => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h
      · rw [hm0 t ht h, h]; omega
      · rw [h]; simpa using hmQ t ht
    have h3' := (mask_blocks_iff hr hgQ).1 h3
    rw [hM]
    apply blocks_congr
    intro t ht
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h
    · rw [hm0 t ht h, h, mul_zero]
    · have := h3' t ht
      rw [h] at this
      simp only [Nat.sub_self, mul_zero, zero_add] at this
      rw [h, mul_one]
      exact Mask.antisymm (h1' t ht) this
  · intro hM
    subst hM
    have hrl : ∀ t < n, r t * l t < Q := fun t ht => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h] <;> simp [hQ, hr t ht]
    refine ⟨(mask_blocks_iff hrl hr).2 fun t ht => ?_, ?_, ?_⟩
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
      · simpa using zero_mask (r t)
      · simpa using Mask.refl (r t)
    · rw [hL]
      refine (mask_blocks_iff hrl hLlt).2 fun t ht => ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
      · simpa using zero_mask 0
      · simpa using (mask_two_pow_sub_one_iff (r t) q).2 (hr t ht)
    · rw [hIL]
      have hgQ : ∀ t < n, (Q - 1) * (1 - l t) + r t * l t < Q := fun t ht => by
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
        · simp
        · simpa using hr t ht
      refine (mask_blocks_iff hr hgQ).2 fun t ht => ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
      · simpa using (mask_two_pow_sub_one_iff (r t) q).2 (hr t ht)
      · simpa using Mask.refl (r t)

/-- **(49) ⟺ (50)**, with the final term `L`. -/
theorem mask49_iff (hq : 1 ≤ q) (hr : ∀ t < n, r t < Q) (hl : ∀ t < n, l t ≤ 1) (J : ℕ) :
    (2 * J ≼ blocks Q n r ∧ J ≼ (Q / 2 - 1) * blocks Q n l ∧
      blocks Q n r ≼ (Q - 1) * (blocks Q n (fun _ => 1) - blocks Q n l) + 2 * J + blocks Q n l) ↔
      J = blocks Q n (fun t => r t / 2 * l t) := by
  have hQ : 0 < Q := by positivity
  have hQ2 : 2 * (Q / 2) = Q := by
    rw [show Q = 2 * 2 ^ (q - 1) by rw [← pow_succ']; congr 1; omega]; omega
  have hL : (Q / 2 - 1) * blocks Q n l = blocks Q n (fun t => (Q / 2 - 1) * l t) :=
    (blocks_smul _ _ _ _).symm
  have hLlt : ∀ t < n, (Q / 2 - 1) * l t < Q := fun t ht => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h] <;> omega
  have hIL : ∀ m : ℕ → ℕ,
      (Q - 1) * (blocks Q n (fun _ => 1) - blocks Q n l) + 2 * blocks Q n m + blocks Q n l =
        blocks Q n (fun t => (Q - 1) * (1 - l t) + 2 * m t + l t) := by
    intro m
    rw [← blocks_sub (fun t ht => hl t ht), ← blocks_smul, ← blocks_smul, ← blocks_add,
      ← blocks_add]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hL] at h2
    have hJ := blocks_of_mask hLlt h2
    set m := digit Q J with hm
    have hmQ : ∀ t < n, m t < Q := fun t _ => digit_lt hQ _ _
    rw [hJ] at h1 h2 h3
    have h2' := (mask_blocks_iff hmQ hLlt).1 h2
    have hm0 : ∀ t < n, l t = 0 → m t = 0 := fun t ht hl0 => by
      have := h2' t ht
      rw [hl0, mul_zero, mask_zero_iff] at this
      exact this
    have hmhalf : ∀ t < n, m t < Q / 2 := fun t ht => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h
      · rw [hm0 t ht h]; omega
      · have := (h2' t ht).le; rw [h] at this; omega
    have h2mQ : ∀ t < n, 2 * m t < Q := fun t ht => by have := hmhalf t ht; omega
    rw [← blocks_smul] at h1
    have h1' := (mask_blocks_iff h2mQ hr).1 h1
    rw [hIL] at h3
    have hgQ : ∀ t < n, (Q - 1) * (1 - l t) + 2 * m t + l t < Q := fun t ht => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h
      · rw [hm0 t ht h, h]; omega
      · rw [h]; have := hmhalf t ht; omega
    have h3' := (mask_blocks_iff hr hgQ).1 h3
    rw [hJ]
    apply blocks_congr
    intro t ht
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h
    · rw [hm0 t ht h, h, mul_zero]
    · have := h3' t ht
      rw [h] at this
      simp only [Nat.sub_self, mul_zero, zero_add] at this
      rw [h, mul_one]
      exact (div_two_of_masks (h1' t ht) this).symm
  · intro hJ
    subst hJ
    have hhalf : ∀ t < n, r t / 2 * l t < Q / 2 := fun t ht => by
      have := hr t ht
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h] <;> omega
    have h2Q : ∀ t < n, 2 * (r t / 2 * l t) < Q := fun t ht => by have := hhalf t ht; omega
    have hQ' : ∀ t < n, r t / 2 * l t < Q := fun t ht => by have := hhalf t ht; omega
    refine ⟨?_, ?_, ?_⟩
    · rw [← blocks_smul]
      refine (mask_blocks_iff h2Q hr).2 fun t ht => ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
      · simpa using zero_mask (r t)
      · rw [mul_one, mask_iff_div2]
        refine ⟨fun h => by omega, ?_⟩
        rw [show 2 * (r t / 2) / 2 = r t / 2 by omega]
        exact Mask.refl _
    · rw [hL]
      refine (mask_blocks_iff hQ' hLlt).2 fun t ht => ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
      · simpa using zero_mask 0
      · have h2 : Q / 2 = 2 ^ (q - 1) := by
          rw [show Q = 2 * 2 ^ (q - 1) by rw [← pow_succ']; congr 1; omega]; omega
        rw [mul_one, mul_one, h2]
        exact (mask_two_pow_sub_one_iff _ _).2 (by rw [← h2]; exact hhalf t ht |>.trans_eq' (by rw [h, mul_one]))
    · rw [hIL]
      have hgQ : ∀ t < n, (Q - 1) * (1 - l t) + 2 * (r t / 2 * l t) + l t < Q := fun t ht => by
        have := hr t ht
        rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h] <;> omega
      refine (mask_blocks_iff hr hgQ).2 fun t ht => ?_
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (hl t ht) with h | h <;> rw [h]
      · simpa using (mask_two_pow_sub_one_iff (r t) q).2 (hr t ht)
      · simp only [Nat.sub_self, mul_zero, zero_add, mul_one]
        rw [mask_iff_div2]
        refine ⟨fun _ => by omega, ?_⟩
        rw [show (2 * (r t / 2) + 1) / 2 = r t / 2 by omega]
        exact Mask.refl _

end

/-- **(52)**: for `0/1` line histories with `L_i`, `L_j` never simultaneously set (`i ≠ j`),
`QL_n ≼ L_i + L_j` says that line `n` is not active at the last step and that every step from
line `n` goes to line `i` or line `j`. -/
theorem branch_iff {q s : ℕ} (hq : 1 ≤ q) {ln li lj : ℕ → ℕ}
    (hn : ∀ t ≤ s, ln t ≤ 1) (hij : ∀ t ≤ s, li t + lj t ≤ 1) :
    2 ^ q * blocks (2 ^ q) (s + 1) ln ≼ blocks (2 ^ q) (s + 1) li + blocks (2 ^ q) (s + 1) lj ↔
      ln s = 0 ∧ ∀ t < s, ln t = 1 → li (t + 1) + lj (t + 1) = 1 := by
  have hQ2 : 2 ≤ 2 ^ q := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hq)
  set g : ℕ → ℕ := fun t => if t < s + 1 then li t + lj t else 0 with hg
  have hR : blocks (2 ^ q) (s + 1) li + blocks (2 ^ q) (s + 1) lj = blocks (2 ^ q) (s + 2) g := by
    rw [← blocks_add, blocks_of_zero_of_ge (by omega : s + 1 ≤ s + 2)
      (fun t ht => by simp only [hg]; rw [if_neg (by omega)])]
    exact blocks_congr fun t ht => by simp only [hg]; rw [if_pos ht]
  rw [blocks_shift, hR]
  have hf : ∀ t < s + 2, (if t = 0 then 0 else ln (t - 1)) < 2 ^ q := fun t ht => by
    split_ifs
    · omega
    · have := hn (t - 1) (by omega); omega
  have hgQ : ∀ t < s + 2, g t < 2 ^ q := fun t ht => by
    simp only [hg]
    split_ifs with h
    · have := hij t (by omega); omega
    · omega
  rw [mask_blocks_iff hf hgQ]
  constructor
  · intro h
    refine ⟨?_, fun t ht h1 => ?_⟩
    · have := h (s + 1) (by omega)
      simp only [hg, if_neg (by omega : ¬ s + 1 = 0), if_neg (by omega : ¬ s + 1 < s + 1),
        Nat.add_sub_cancel, mask_zero_iff] at this
      exact this
    · have := h (t + 1) (by omega)
      simp only [hg, if_neg (by omega : ¬ t + 1 = 0), if_pos (by omega : t + 1 < s + 1),
        Nat.add_sub_cancel, h1] at this
      have hle := hij (t + 1) (by omega)
      have hpos := this.le
      omega
  · rintro ⟨hs, hstep⟩ t ht
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · simpa using zero_mask (g 0)
    · simp only [if_neg (by omega : ¬ t = 0)]
      have hl1 := hn (t - 1) (by omega)
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hl1 with h0 | h1
      · rw [h0]; exact zero_mask _
      · have ht' : t - 1 < s := by
          by_contra hc
          have : t - 1 = s := by omega
          rw [this] at h1; omega
        have := hstep (t - 1) ht' h1
        simp only [hg, if_pos (by omega : t < s + 1)]
        rw [h1, show t - 1 + 1 = t by omega] at *
        rw [this]
        exact Mask.refl 1

end JM1984
