import DiophantineConsistency.CurrentOneHot2011
import DiophantineConsistency.CurrentCellLabels2011

/-!
# Every actual current zero has decoded cell labels

Selector counts and fractional phase are derived from the same arithmetic
Facts before applying the full clause decoder. Empty cells remain allowed.
The actual Start South word and the fixed physical941 South calibration
are exposed for the subsequent whole-field alignment argument.
-/

namespace DiophantineConsistency.CurrentDecodedWindow2011

open CurrentMasks2011 CurrentPolynomialWindow2011 CurrentOneHot2011
  CurrentCellLabels2011 CurrentClause2011 WangTiles942
open scoped BigOperators

set_option Elab.async false

variable {N : ℕ} [NeZero (N * 2011)]

theorem facts_decode_cell (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    CellDecoded c carry
      ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)) b ∧
      carry (b + 1005) = 0 := by
  have hphase := (facts_count_phase v x c carry digits h).2
  have hcount := literal_count_le_one c carry digits _ h.boolean h.support h.carry_bound
    h.carry_equation h.mask_tests b hb
  exact decode_cell c carry digits _ h.boolean h.support h.carry_bound
    h.carry_equation h.mask_tests hphase b hb hcount

/-- The actual forced Start has South complement510, before occupation
or whole-field alignment is known. -/
theorem facts_start_south (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    binaryWord (fun j => c (((942 + j : ℕ) : ZMod (N * 2011)))) 9 = 510 := by
  have hdecoded := (facts_decode_cell v x c carry digits h 0 (by simp)).1
  have hi : selectorValue c 0 0 = 1 := by
    simpa only [selectorValue, physicalPosition_zero, Nat.cast_zero, zero_add] using h.origin
  have hword := hdecoded.word_of_selected 0 hi
  have hs := (labels_of_word c 0 h.boolean 0 hword).2.2.2
  simpa only [zero_add, start_zero] using hs

/-- A selected physical terminal position has one fixed actual South value.
No assumption excludes its real possible511 value. -/
theorem facts_terminal_south (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (hterminal : c (b + 941) = 1) :
    binaryWord (fun j => c (b + ((942 + j : ℕ) : ZMod (N * 2011)))) 9 =
      511 - (tile (physicalEquiv.symm (941 : Fin 942))).south := by
  have hp := congrArg Fin.val (physicalEquiv.apply_symm_apply (941 : Fin 942))
  change physicalPosition (physicalEquiv.symm (941 : Fin 942)) = 941 at hp
  have hi : selectorValue c b (physicalEquiv.symm (941 : Fin 942)) = 1 := by
    simpa only [selectorValue, hp, Nat.cast_ofNat] using hterminal
  have hd := (facts_decode_cell v x c carry digits h b hb).1
  have hw := hd.word_of_selected (physicalEquiv.symm (941 : Fin 942)) hi
  exact (labels_of_word c b h.boolean _ hw).2.2.2

def DecodedWindow (v : Fin 14 → ℤ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ x : Fin 31 → ℕ, ∃ c carry digits : ZMod (N * 2011) → ℕ,
    Facts v N x c carry digits ∧
    ∀ b : ZMod (N * 2011), b.val % 2011 = 0 →
      CellDecoded c carry
        ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)) b ∧
        carry (b + 1005) = 0

theorem polynomial_zero_decoded_window (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, DecodedWindow v N hN := by
  obtain ⟨N, hN, hwin⟩ := polynomial_zero_window v hv hz
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨x, c, carry, digits, h⟩ := hwin
  exact ⟨N, hN, x, c, carry, digits, h, facts_decode_cell v x c carry digits h⟩

end DiophantineConsistency.CurrentDecodedWindow2011
