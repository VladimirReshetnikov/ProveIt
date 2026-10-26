import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
# Full doubled-clause decoding for the 2011-field presentation

This is arithmetic over natural numbers, independent of the physical stencil.
The incoming carry and both Boolean contributions remain present while the
34-bit word is decoded. In particular, no zero-carry hypothesis is used.
-/

namespace DiophantineConsistency.DoubledClause2011

set_option Elab.async false

def wordBase : ℕ := 2 ^ 34
def radix : ℕ := 2 ^ 47
def mask : ℕ := 2 ^ 45 - 4

/-- The full mask tests precisely bits 2 through 44. -/
theorem mask_iff (x : ℕ) : x &&& mask = 0 ↔ x % 2 ^ 45 ≤ 3 := by
  have hd : (x &&& mask) / 4 = (x / 4) % 2 ^ 43 := by
    calc
      (x &&& mask) / 4 = (x &&& mask) / 2 / 2 := by
        rw [Nat.div_div_eq_div_mul]
      _ = (x / 2 / 2) &&& (2 ^ 43 - 1) := by
        rw [Nat.and_div_two, Nat.and_div_two]
        rfl
      _ = (x / 4) % 2 ^ 43 := by
        rw [Nat.and_two_pow_sub_one_eq_mod, Nat.div_div_eq_div_mul]
  have hm : (x &&& mask) % 4 = 0 := by
    change (x &&& mask) % 2 ^ 2 = 0
    rw [Nat.and_mod_two_pow]
    norm_num [mask]
  constructor
  · intro h
    rw [h] at hd
    norm_num at hd ⊢
    omega
  · intro h
    norm_num at hd h
    omega

/-- The ordinary raw clause, before reduction to one radix field. -/
def raw (n W u k t b : ℕ) : ℕ :=
  2 * n + 2048 * ((wordBase - u) * n + W) + k + t + b

def digit (n W u k t b : ℕ) : ℕ := raw n W u k t b % radix

/-- Every bounded input already fits in one field, whether or not its mask
passes. This is derived from the unsigned input ranges, not assumed. -/
theorem raw_lt_radix {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) :
    raw n W u k t b < radix := by
  by_cases hn0 : n = 0
  · subst n
    simp only [raw, Nat.mul_zero, Nat.zero_add]
    norm_num [wordBase, radix] at hW hu ⊢
    omega
  · have hn1 : n = 1 := by omega
    subst n
    simp only [raw, Nat.mul_one]
    norm_num [wordBase, radix] at hW hu ⊢
    omega

theorem digit_eq_raw {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) :
    digit n W u k t b = raw n W u k t b :=
  Nat.mod_eq_of_lt (raw_lt_radix hn hW hu hk ht hb)

/-- The outgoing carry is recovered without any mask or incoming-zero premise. -/
theorem outgoing_carry_zero {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) :
    raw n W u k t b / radix = 0 :=
  Nat.div_eq_of_lt (raw_lt_radix hn hW hu hk ht hb)

/-- An empty cell has zero copied word and at most three low units. -/
theorem decode_empty {W u k t b : ℕ}
    (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1)
    (hmask : digit 0 W u k t b &&& mask = 0) :
    W = 0 ∧ k + t + b ≤ 3 := by
  rw [digit_eq_raw (by omega) hW hu hk ht hb] at hmask
  have h := (mask_iff _).mp hmask
  simp only [raw, Nat.mul_zero, Nat.zero_add] at h
  norm_num [wordBase] at hW hu h
  omega

/-- An occupied cell recovers all 34 bits, allowing the incoming carry,
temporal bit and bare bit to compete for its one remaining low unit. -/
theorem decode_occupied {W u k t b : ℕ}
    (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1)
    (hmask : digit 1 W u k t b &&& mask = 0) :
    W = u ∧ k + t + b ≤ 1 := by
  rw [digit_eq_raw (by omega) hW hu hk ht hb] at hmask
  have h := (mask_iff _).mp hmask
  simp only [raw, Nat.mul_one] at h
  norm_num [wordBase] at hW hu h
  omega

/-- The empty and occupied cases exhaust the actual masked digit. -/
theorem decode {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1)
    (hmask : digit n W u k t b &&& mask = 0) :
    (n = 0 ∧ W = 0 ∧ k + t + b ≤ 3) ∨
    (n = 1 ∧ W = u ∧ k + t + b ≤ 1) := by
  by_cases hn0 : n = 0
  · subst n
    exact Or.inl ⟨rfl, decode_empty hW hu hk ht hb hmask⟩
  · have hn1 : n = 1 := by omega
    subst n
    exact Or.inr ⟨rfl, decode_occupied hW hu hk ht hb hmask⟩

/-- Every empty low value allowed by the mask is a valid raw clause. -/
theorem empty_converse {u k t b : ℕ} (hsmall : k + t + b ≤ 3) :
    raw 0 0 u k t b = k + t + b ∧
    digit 0 0 u k t b &&& mask = 0 ∧
    raw 0 0 u k t b < radix ∧ raw 0 0 u k t b / radix = 0 := by
  have hr : raw 0 0 u k t b = k + t + b := by simp [raw]
  have hbound : raw 0 0 u k t b < radix := by
    rw [hr]
    norm_num [radix]
    omega
  refine ⟨hr, ?_, hbound, Nat.div_eq_of_lt hbound⟩
  change (raw 0 0 u k t b % radix) &&& mask = 0
  rw [Nat.mod_eq_of_lt hbound, hr, mask_iff]
  exact le_trans (Nat.mod_le _ _) hsmall

/-- An occupied matching word gives exactly the untested high bit together
with its two or three low units. -/
theorem occupied_converse {u k t b : ℕ}
    (hu : u < wordBase) (hsmall : k + t + b ≤ 1) :
    raw 1 u u k t b = 2 ^ 45 + 2 + (k + t + b) ∧
    digit 1 u u k t b &&& mask = 0 ∧
    raw 1 u u k t b < radix ∧ raw 1 u u k t b / radix = 0 := by
  have hr : raw 1 u u k t b = 2 ^ 45 + 2 + (k + t + b) := by
    simp only [raw, Nat.mul_one]
    norm_num [wordBase] at hu ⊢
    omega
  have hbound : raw 1 u u k t b < radix := by
    rw [hr]
    norm_num [radix]
    omega
  refine ⟨hr, ?_, hbound, Nat.div_eq_of_lt hbound⟩
  change (raw 1 u u k t b % radix) &&& mask = 0
  rw [Nat.mod_eq_of_lt hbound, hr, mask_iff]
  norm_num
  omega

theorem mask_iff_decoded {n W u k t b : ℕ}
    (hn : n ≤ 1) (hW : W < wordBase) (hu : u < wordBase)
    (hk : k ≤ 57) (ht : t ≤ 1) (hb : b ≤ 1) :
    digit n W u k t b &&& mask = 0 ↔
      (n = 0 ∧ W = 0 ∧ k + t + b ≤ 3) ∨
      (n = 1 ∧ W = u ∧ k + t + b ≤ 1) := by
  refine ⟨decode hn hW hu hk ht hb, ?_⟩
  rintro (⟨rfl, rfl, hsmall⟩ | ⟨rfl, rfl, hsmall⟩)
  · exact (empty_converse hsmall).2.1
  · exact (occupied_converse hu hsmall).2.1

end DiophantineConsistency.DoubledClause2011
