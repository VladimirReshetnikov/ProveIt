import DiophantineConsistency.NativeLocalMask54
import DiophantineConsistency.NativeCellRecipe54

/-! # The literal stencil's local coefficient sum is the checked native clause -/

namespace DiophantineConsistency.NativeCellWord54

open NativeStencil54 NativeSparseDigits54 NativeLocalMask54 NativeClauseBits54
  NativeSelectorClause54 NativeLocalCoefficients54 NativeModesData54
open scoped BigOperators

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

variable {N : ℕ} [NeZero (N * cellLength)]

def selectors (c : ZMod (N * cellLength) → ℕ) (b : ZMod (N * cellLength)) (i : Fin 457) : ℕ :=
  c (b + i.val)
def copiedBits (c : ZMod (N * cellLength) → ℕ) (b : ZMod (N * cellLength)) (i : Fin 42) : ℕ :=
  c (b + copyPosition i)
def rightBits (c : ZMod (N * cellLength) → ℕ) (b : ZMod (N * cellLength)) (i : Fin 8) : ℕ :=
  c (b + (567+i.val : ℕ))
def leftBits (c : ZMod (N * cellLength) → ℕ) (b : ZMod (N * cellLength)) (i : Fin 8) : ℕ :=
  c (b + (575+i.val : ℕ))

/-- The exact 520-entry local sum, with its actual bit/selector positions,
is the local decoder's nativeWord; no equality is postulated. -/
theorem localCell_eq_nativeWord (c : ZMod (N * cellLength) → ℕ)
    (b : ZMod (N * cellLength)) :
    localCell c b = nativeWord (selectors c b)
      (binaryValue (rightBits c b)) (binaryValue (leftBits c b))
      (c (b + 583)) (binaryValue (copiedBits c b))
      (copiedBits c b 0) (c (b + 1203)) (c (b + 1807)) := by
  have h := NativeCellRecipe54.coefficient_sum_eq_nativeWord
    (fun j : ℕ => c (b + (j : ZMod (N * cellLength))))
  unfold selectors copiedBits rightBits leftBits
  rw [show copyPosition (0 : Fin 42) = 539 from rfl]
  simpa only [localCell, Nat.cast_ofNat] using h

/-- Every ordinary position in a cell is Boolean, derived from the
reconstructed periodic capacities. -/
theorem cell_bit (c : ZMod (N * cellLength) → ℕ)
    (hc : ∀ k, c k < 2 ^ periodicBits k) (b : ZMod (N * cellLength))
    (hb : b.val % cellLength = 0) {j : ℕ} (hj : j < cellLength) (hd : j ≠ 507) :
    c (b + (j : ZMod (N * cellLength))) ≤ 1 := by
  apply assignment_boolean c hc
  rw [addition_residue,Nat.add_mod,hb,zero_add,Nat.mod_mod,Nat.mod_eq_of_lt hj]
  exact hd

omit [NeZero (N * cellLength)] in
theorem binaryValue_lt {m : ℕ} (z : Fin m → ℕ) (hz : ∀ i, z i ≤ 1) :
    binaryValue z < 2 ^ m := by
  have he : Nat.ofDigits 2 (List.ofFn z) = binaryValue z := by
    rw [Jones1982.ofDigits_ofFn]
    rfl
  rw [← he]
  have hh := Nat.ofDigits_lt_base_pow_length (by decide : 1 < 2)
    (show ∀ a ∈ List.ofFn z, a < 2 by
      intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      have hi := hz i
      omega)
  simpa only [List.length_ofFn] using hh

omit [NeZero (N * cellLength)] in
theorem binaryValue_mod_two (z : Fin 42 → ℕ) (hz : z 0 ≤ 1) : binaryValue z % 2 = z 0 := by
  have he : Nat.ofDigits 2 (List.ofFn z) = binaryValue z := by
    rw [Jones1982.ofDigits_ofFn]
    rfl
  rw [← he,List.ofFn_succ,Nat.ofDigits_cons,Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

end DiophantineConsistency.NativeCellWord54
