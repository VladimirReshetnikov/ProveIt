import DiophantineConsistency.NativeCleanBands54

/-! # Sparse temporal rotations leave one member of each clause pair clean -/

namespace DiophantineConsistency.NativeTemporalSupport54

open NativeStencil54 NativeSparseDigits54 NativeCleanBands54
  NativeCyclicRotation NativeCyclicConvolution

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem lower_dummy_mem : 508 ∈ support := by
  apply List.mem_toFinset.mpr
  rw [NativeLowPort54.positions, ← OnePageTuple54.assignmentPositions_eq]
  decide

variable {N : ℕ} [NeZero (N * cellLength)]

/-- Binary carries outside the support vanish: the only possible
non-Boolean predecessor is507, whose successor508 is already supported. -/
theorem shiftDigits_sparse (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) {e : ℕ} (he : e ≤ 88)
    (k : ZMod (N * cellLength)) (hk : k.val % cellLength ∉ support) :
    shiftDigits radix (2 ^ e) c k = 0 := by
  have hzero := assignment_sparse c hc k hk
  have hprev : (k - 1).val % cellLength ≠ 507 := by
    intro hp
    have hh := subtraction_residue k 1
    norm_num only [Nat.cast_one] at hh
    have hh' : ((k - 1).val % cellLength + 1) % cellLength = k.val % cellLength := by
      simpa only [Nat.add_mod,Nat.mod_mod] using hh
    rw [hp] at hh'
    norm_num only [cellLength,Nat.reduceAdd,Nat.reduceMod] at hh'
    exact hk (hh' ▸ lower_dummy_mem)
  have hb := assignment_boolean c hc (k - 1) hprev
  have hpow : 2 ^ e ≤ 2 ^ 88 := Nat.pow_le_pow_right (by decide) he
  have hlt : 2 ^ e * c (k - 1) < radix := by
    have hmul := Nat.mul_le_mul hpow hb
    norm_num only [mul_one] at hmul
    have hh : 2 ^ 88 < radix := by decide
    omega
  simp only [shiftDigits,hzero,Nat.mul_zero,Nat.zero_mod,zero_add,Nat.div_eq_of_lt hlt]

/-- No partial bit phase introduces a new position outside the rotated
literal support. This includes the upper-dummy carry at phase88. -/
theorem binaryRotation_sparse (W : ℕ) (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (k : ZMod (N * cellLength))
    (hk : (k - ((W / 89 : ℕ) : ZMod (N * cellLength))).val % cellLength ∉ support) :
    binaryRotation 89 W c k = 0 := by
  change shiftDigits radix (2 ^ (W % 89)) c
    (k - ((W / 89 : ℕ) : ZMod (N * cellLength))) = 0
  exact shiftDigits_sparse c hc (by have := Nat.mod_lt W (by decide : 0 < 89); omega) _ hk

private theorem no_difference_606 (a b : ℕ) (ha : CoarseSupport a) (hb : CoarseSupport b) :
    (a + 606) % cellLength ≠ b := by
  unfold CoarseSupport cellLength at *
  rcases ha with ha | rfl | rfl <;>
    rcases hb with hb | rfl | rfl <;> omega

/-- Every pair of positions separated by606 has a zero temporal digit
at one member. The bit phase and whole-digit rotation are arbitrary. -/
theorem clause_pair_one_zero (W : ℕ) (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (l r : ZMod (N * cellLength))
    (hr : r = l + 606) :
    binaryRotation 89 W c l = 0 ∨ binaryRotation 89 W c r = 0 := by
  by_cases hl : (l - ((W / 89 : ℕ) : ZMod (N * cellLength))).val % cellLength ∈ support
  · by_cases hrr : (r - ((W / 89 : ℕ) : ZMod (N * cellLength))).val % cellLength ∈ support
    · have hh := subtraction_residue (r - ((W / 89 : ℕ) : ZMod (N * cellLength))) 606
      have hi : r - ((W / 89 : ℕ) : ZMod (N * cellLength)) - (606 : ZMod (N * cellLength)) =
          l - ((W / 89 : ℕ) : ZMod (N * cellLength)) := by rw [hr]; abel
      change ((r - ((W / 89 : ℕ) : ZMod (N * cellLength)) - (606 : ZMod (N * cellLength))).val + 606) %
        cellLength = (r - ((W / 89 : ℕ) : ZMod (N * cellLength))).val % cellLength at hh
      rw [hi] at hh
      have hh' : ((l - ((W / 89 : ℕ) : ZMod (N * cellLength))).val % cellLength + 606) % cellLength =
          (r - ((W / 89 : ℕ) : ZMod (N * cellLength))).val % cellLength := by
        simpa only [Nat.add_mod,Nat.mod_mod] using hh
      exact False.elim (no_difference_606 _ _ (support_coarse hl) (support_coarse hrr) hh')
    · exact Or.inr (binaryRotation_sparse W c hc r hrr)
  · exact Or.inl (binaryRotation_sparse W c hc l hl)

end DiophantineConsistency.NativeTemporalSupport54
