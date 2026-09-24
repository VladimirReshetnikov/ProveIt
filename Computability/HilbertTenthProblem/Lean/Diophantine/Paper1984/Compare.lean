import Diophantine.Paper1984.Blocks

/-!
# The conditional-transfer conditions (35)–(37)

The second condition used for a conditional transfer at line `i` has the shape

  `Q L_i ≼ L_n + Q I + 2U − 2V`

with `n = k` (the target) for `IF Rj < Rm GO TO Lk` and `n = i+1` for
`IF Rj ≤ Rm GO TO Lk`, and with `U, V` the encoded operand histories.  The paper
reads it block by block: at time `t` the block of `Q I + 2U − 2V` contributes a
carry exactly when `u_t ≥ v_t`, so the lowest bit of block `t+1` is
`l_{n,t+1} XOR [u_t ≥ v_t]`, and the mask condition says that if line `i` is
executed at time `t` then the machine is at line `n` at time `t+1` iff `u_t < v_t`.

`compare_cond` proves exactly this, including the carry propagation the paper
leaves implicit: the block values are `≤ 2Q − 2` (hypothesis `hy`, which holds
because register contents at times `1 ≤ t < s` are at most `x + s − 1 < Q/2 − 1`),
so all carries are `0` or `1`, and when line `i` is executed at time `t` the
line `n ≠ i` is not, so the carry out of block `t` is `[u_t ≥ v_t]`.
-/

namespace JM1984

open Finset

/-- The meaning of `Q L_i ≼ L_n + Q I + 2U − 2V` for block-encoded histories. -/
theorem compare_cond {q s Q : ℕ} (hQ : Q = 2 ^ q) (hq : 2 ≤ q)
    {li ln u v : ℕ → ℕ}
    (hli : ∀ t, li t ≤ 1) (hln : ∀ t, ln t ≤ 1)
    (hdisj : ∀ t, li t = 1 → ln t = 0)
    (hlis : ∀ t, li t = 1 → t < s)
    (hu : ∀ t, 2 * u t < Q) (hv : ∀ t, 2 * v t < Q)
    (hy : ∀ t, 1 ≤ t → t < s → ln t + 2 * u t + 2 ≤ Q + 2 * v t) :
    Q * blocks Q (s + 1) li ≼
      blocks Q (s + 1) ln + Q * blocks Q (s + 1) (fun _ => 1) + 2 * blocks Q (s + 1) u
        - 2 * blocks Q (s + 1) v
    ↔ ∀ t, li t = 1 → (ln (t + 1) = 1 ↔ u t < v t) := by
  subst hQ
  have hQ4 : 4 ≤ 2 ^ q := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) hq
  have hQ0 : 0 < 2 ^ q := by omega
  have hQ2 : 2 ∣ 2 ^ q := dvd_pow_self 2 (by omega)
  have hQ2' : 2 ^ q % 2 = 0 := Nat.mod_eq_zero_of_dvd hQ2
  -- the block values before carries
  set y : ℕ → ℕ := fun t => if t ≤ s then ln t + 2 ^ q + 2 * u t - 2 * v t else 0 with hy_def
  have hR : blocks (2 ^ q) (s + 1) ln + 2 ^ q * blocks (2 ^ q) (s + 1) (fun _ => 1)
      + 2 * blocks (2 ^ q) (s + 1) u - 2 * blocks (2 ^ q) (s + 1) v
      = blocks (2 ^ q) (s + 1) y := by
    rw [← blocks_smul, ← blocks_smul, ← blocks_smul, ← blocks_add, ← blocks_add, ← blocks_sub]
    · apply blocks_congr
      intro t ht
      simp only [y, mul_one]
      rw [if_pos (by omega)]
    · intro t ht
      have := hv t
      omega
  have hy0 : y 0 < 2 * 2 ^ q := by
    simp only [y, if_pos (Nat.zero_le s)]
    have := hu 0; have := hln 0
    omega
  have hy1 : ∀ t, 1 ≤ t → t < s → y t + 2 ≤ 2 * 2 ^ q := by
    intro t h1 h2
    simp only [y, if_pos (by omega : t ≤ s)]
    have := hy t h1 h2; have := hv t
    omega
  have hys : y s < 2 * 2 ^ q := by
    simp only [y, if_pos le_rfl]
    have := hu s; have := hln s
    omega
  have hcar : ∀ t ≤ s, carry (2 ^ q) y t ≤ 1 := carry_le_one' hQ0 hy0 hy1
  have hcar1 : carry (2 ^ q) y (s + 1) ≤ 2 := by
    rw [carry_succ, Nat.div_le_iff_le_mul_add_pred hQ0]
    have := hcar s le_rfl
    omega
  have hys1 : y (s + 1) = 0 := by simp [y]
  have hcar2 : carry (2 ^ q) y (s + 2) = 0 := by
    rw [carry_succ, hys1, Nat.zero_add]
    exact Nat.div_eq_of_lt (by omega)
  have hR2 : blocks (2 ^ q) (s + 1) y = blocks (2 ^ q) (s + 2) (normal (2 ^ q) y) := by
    rw [← blocks_of_zero_of_ge (n := s + 1) (m := s + 2) (by omega)
        (fun t ht => by simp [y]; omega),
      blocks_normal (2 ^ q) y (s + 2), hcar2]
    simp
  -- the parity computation at block `t + 1` when line `i` is executed at time `t`
  have hkey : ∀ t, t < s → li t = 1 →
      (normal (2 ^ q) y (t + 1) % 2 = 1 ↔ (ln (t + 1) = 1 ↔ u t < v t)) := by
    intro t hts hli1
    have hln0 := hdisj t hli1
    have hc := hcar t (by omega)
    have hyt : y t = 2 ^ q + 2 * u t - 2 * v t := by
      simp only [y, if_pos (by omega : t ≤ s), hln0, Nat.zero_add]
    have hyt1 : y (t + 1) = ln (t + 1) + 2 ^ q + 2 * u (t + 1) - 2 * v (t + 1) := by
      simp only [y, if_pos (by omega : t + 1 ≤ s)]
    have hcar_t1 : carry (2 ^ q) y (t + 1) = if u t < v t then 0 else 1 := by
      rw [carry_succ, hyt]
      have hu' := hu t
      have hv' := hv t
      split_ifs with h
      · apply Nat.div_eq_of_lt
        omega
      · apply Nat.div_eq_of_lt_le <;> omega
    unfold normal
    rw [Nat.mod_mod_of_dvd _ hQ2, hyt1, hcar_t1]
    have := hln (t + 1)
    have := hv (t + 1)
    split_ifs with h <;> omega
  rw [hR, hR2, blocks_shift,
    mask_blocks_iff (fun t _ => by split_ifs <;> (first | omega | (have := hli (t - 1); omega)))
      (fun t _ => normal_lt hQ0 y t),
    forall_lt_succ']
  simp only [↓reduceIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]
  constructor
  · rintro ⟨-, H⟩ t hli1
    have hts := hlis t hli1
    have := H t (by omega)
    rw [mask_of_le_one_iff (hli t)] at this
    exact (hkey t hts hli1).1 (this hli1)
  · intro H
    refine ⟨zero_mask _, fun t _ => ?_⟩
    rw [mask_of_le_one_iff (hli t)]
    intro hli1
    exact (hkey t (hlis t hli1) hli1).2 (H t hli1)

end JM1984
