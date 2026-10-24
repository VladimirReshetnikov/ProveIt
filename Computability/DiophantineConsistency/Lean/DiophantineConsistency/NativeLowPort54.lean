import DiophantineConsistency.NativeStencil54

/-! # Exact compact54 low-mask recipe and its origin residue -/

namespace DiophantineConsistency.NativeLowPort54

open NativeStencil54

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- The forbidden selector at position1 is omitted from the cleared bits. -/
def positions : List ℕ := (entries.map Prod.fst).filter (fun e => e != 1)

theorem positions_length : positions.length = 519 := by decide

theorem positions_head : positions = 0 :: positions.tail := by decide

private theorem positive_tail : positions.tail.all (fun e => decide (0 < e)) = true := by decide

private theorem bounded_positions : positions.all (fun e => decide (e ≤ 1807)) = true := by decide

def removedWord (r : ℕ) : ℕ := (positions.map fun e => r ^ e).sum + 2 * r ^ 507

/-- This is the whole native MC recipe, including the upper dummy bit. -/
def lowPort : ℕ := radix ^ cellLength - 1 - removedWord radix

theorem removedWord_bound {r : ℕ} (hr : 1 ≤ r) : removedWord r ≤ 521 * r ^ 1807 := by
  have hs : (positions.map fun e => r ^ e).sum ≤ 519 * r ^ 1807 := by
    have hb := List.sum_le_card_nsmul (positions.map fun e => r ^ e) (r ^ 1807) (by
      intro x hx
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      have heB : e ≤ 1807 := of_decide_eq_true ((List.all_eq_true.mp bounded_positions) e he)
      exact Nat.pow_le_pow_right hr heB)
    simpa only [List.length_map, positions_length, nsmul_eq_mul, Nat.cast_id] using hb
  have he : r ^ 507 ≤ r ^ 1807 := Nat.pow_le_pow_right hr (by decide)
  unfold removedWord
  omega

theorem lowPort_exact : lowPort + removedWord radix + 1 = radix ^ cellLength := by
  have hr : 522 ≤ radix := by decide
  have hp : 1 ≤ radix ^ 1807 := one_le_pow₀ (by have := hr; omega)
  have hb := removedWord_bound (r := radix) (by have := hr; omega)
  have hs : removedWord radix + 1 ≤ radix ^ 1808 := by
    rw [show 1808 = 1807 + 1 by decide, pow_succ]
    calc
      removedWord radix + 1 ≤ 522 * radix ^ 1807 := by omega
      _ ≤ radix ^ 1807 * radix := by
        calc
          522 * radix ^ 1807 ≤ radix * radix ^ 1807 :=
            Nat.mul_le_mul_right (radix ^ 1807) hr
          _ = radix ^ 1807 * radix := Nat.mul_comm _ _
  have ht : radix ^ 1808 ≤ radix ^ cellLength :=
    Nat.pow_le_pow_right (by have := hr; omega) (by decide)
  unfold lowPort
  omega

theorem removedWord_mod_radix : removedWord radix % radix = 1 := by
  have ht : ((positions.tail.map fun e => radix ^ e).sum) % radix = 0 := by
    apply Nat.ModEq.listSum_map_zero
    intro e he
    have he0 : 0 < e := of_decide_eq_true ((List.all_eq_true.mp positive_tail) e he)
    change radix ^ e % radix = 0
    rw [Nat.pow_mod, Nat.mod_self, zero_pow (by omega : e ≠ 0), Nat.zero_mod]
  have hp : radix ^ 507 % radix = 0 := by
    rw [Nat.pow_mod, Nat.mod_self, zero_pow (by decide : 507 ≠ 0), Nat.zero_mod]
  unfold removedWord
  conv_lhs => rw [positions_head]
  simp only [List.map_cons, List.sum_cons, pow_zero, Nat.add_mod,
    Nat.mul_mod, Nat.mod_mod, ht, hp]
  norm_num [radix]

attribute [local irreducible] lowPort removedWord

/-- The full defining low-mask expression has the residue required to
force the source's complete origin digit, without evaluating its huge value. -/
theorem lowPort_mod_radix : lowPort % radix = radix - 2 := by
  have hp : radix ^ cellLength % radix = 0 := by
    rw [Nat.pow_mod, Nat.mod_self, zero_pow (by decide : cellLength ≠ 0), Nat.zero_mod]
  have he := congrArg (fun z : ℕ => z % radix) lowPort_exact
  simp only [Nat.add_mod, Nat.mod_mod, removedWord_mod_radix, hp] at he
  have hb := Nat.mod_lt lowPort (by decide : 0 < radix)
  norm_num only [radix] at he hb ⊢
  omega

end DiophantineConsistency.NativeLowPort54
