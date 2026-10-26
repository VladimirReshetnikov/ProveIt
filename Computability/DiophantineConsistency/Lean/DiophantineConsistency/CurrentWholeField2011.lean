import DiophantineConsistency.CurrentDecodedWindow2011
import DiophantineConsistency.CurrentCopyParity2011
import DiophantineConsistency.CurrentFieldOffsets2011
import DiophantineConsistency.CurrentSouthShift2011
import DiophantineConsistency.NativeFieldCycles2011

/-!
# Whole-field alignment of the actual current polynomial window

The sole native premise is the original polynomial-window `Facts`.
Its masks first give the selector bound, fractional phase, decoded South
words and actual copy identities. The forced Start then reduces the field
offset to0,19,20. The two remaining offsets contradict the generic finite
cycle and residue lemmas. No occupation, unique Start, or marker-value
premise is added, and the original window witnesses are retained.
-/

namespace DiophantineConsistency.CurrentWholeField2011

open CurrentPolynomialWindow2011 CurrentDecodedWindow2011 CurrentOneHot2011
  CurrentCellLabels2011 CurrentCellTranslation2011 CurrentSouthShift2011
open scoped BigOperators

set_option Elab.async false
set_option maxHeartbeats 2000000

/-- Only the first three Boolean bits are needed to extract Start's
two South ones. The nine-bit word is not enumerated. -/
theorem binaryWord_510_bits (f : ℕ → ℕ) (hf : ∀ j, j < 9 → f j ≤ 1)
    (hw : binaryWord f 9 = 510) : f 1 = 1 ∧ f 2 = 1 := by
  have hs := binaryWord_append f 3 6
  have hl := binaryWord_lt f 3 (fun j hj => hf j (by omega))
  norm_num only [Nat.reduceAdd, Nat.reducePow] at hs hl
  have hp : binaryWord f 3 = 6 := by omega
  have h0 := hf 0 (by decide)
  have h1 := hf 1 (by decide)
  have h2 := hf 2 (by decide)
  norm_num [binaryWord, Finset.sum_range_succ] at hp
  omega

variable {N : ℕ} [NeZero (N * 2011)]

/-- The two actual physical South fields used in the coarse offset test
are derived from the literal Start tile and the decoded clause. -/
theorem facts_start_bits (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    c 943 = 1 ∧ c 944 = 1 := by
  have hs := binaryWord_510_bits
    (fun j => c (((942+j : ℕ) : ZMod (N * 2011))))
    (fun _ _ => h.boolean _) (facts_start_south v x c carry digits h)
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using hs

/-- The actual physical nine-copy and marker equalities, before whole-field
alignment. Every reset, mask and one-selector premise comes from `Facts`. -/
theorem facts_copy_marker (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : Cell N) :
    let W := (Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)
    (∀ j : Fin 9,
      c ((b : ZMod (N * 2011)) + ((942+j.val : ℕ) : ZMod (N * 2011))) =
      c ((b : ZMod (N * 2011)) + ((960+j.val : ℕ) : ZMod (N * 2011)) -
        ((W/47 : ℕ) : ZMod (N * 2011)))) ∧
    c (b : ZMod (N * 2011)) =
      c ((b : ZMod (N * 2011)) + 1004 - ((W/47 : ℕ) : ZMod (N * 2011))) := by
  have hp := facts_count_phase v x c carry digits h
  exact CurrentCopyParity2011.copy_marker_equalities _ hp.2 c carry digits
    h.boolean h.support h.carry_bound h.carry_recurrence h.carry_equation h.mask_tests
    b b.property (hp.1 b b.property)

/-- Whole-field alignment follows from the original window facts alone.
The terminal selector's South value is fixed by the actual tile table;
it is not assumed to be non511, and the real511 self-loop is allowed. -/
theorem facts_whole_field (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    (((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) / 47) % 2011 = 0 := by
  let W := (Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47 * (N * 2011)
  let t := W/47
  change t % 2011 = 0
  have hcount := (facts_count_phase v x c carry digits h).1
  have hcopy := facts_copy_marker v x c carry digits h
  have hstart : southWord c (0 : Cell N) = 510 := by
    simpa only [southWord, coe_zero, zero_add] using facts_start_south v x c carry digits h
  have hbits := facts_start_bits v x c carry digits h
  have hm : c (1004 - (t : ZMod (N * 2011))) = 1 := by
    have hh := (hcopy (0 : Cell N)).2
    simpa only [coe_zero, zero_add, h.origin] using hh.symm
  have h961 : c (961 - (t : ZMod (N * 2011))) = 1 := by
    have hh := (hcopy (0 : Cell N)).1 (1 : Fin 9)
    norm_num only [coe_zero, Fin.val_one, Nat.reduceAdd, Nat.cast_ofNat, zero_add] at hh
    exact hh.symm.trans hbits.1
  have h962 : c (962 - (t : ZMod (N * 2011))) = 1 := by
    have hh := (hcopy (0 : Cell N)).1 (2 : Fin 9)
    norm_num only [coe_zero, Fin.reduceFinMk, Nat.reduceAdd, Nat.cast_ofNat, zero_add] at hh
    exact hh.symm.trans hbits.2
  have habstract (b : Cell N) : CurrentClause2011.selectorCount c b ≤ 1 :=
    literal_count_le_one c carry digits W h.boolean h.support h.carry_bound
      h.carry_equation h.mask_tests b b.property
  rcases CurrentFieldOffsets2011.coarse_offset c t h.support habstract hm h961 h962 with
    hr | hr | hr
  · exact hr
  · have hex : ∀ b : Cell N, southWord c b ≠ 510 := by
      apply NativeFieldCycles2011.offset19_excludes_510 (theta t).symm (southWord c)
        (fun b => c ((b : ZMod (N * 2011)) + 941))
        (511 - (WangTiles942.tile (WangTiles942.physicalEquiv.symm (941 : Fin 942))).south)
      · exact southWord_lt c h.boolean
      · intro b
        exact h.boolean _
      · intro b
        have hh := offset19_word c h.boolean t ((theta t).symm b) hr
          (hcopy ((theta t).symm b)).1
        simp only [Equiv.apply_symm_apply] at hh
        have hb := southWord_lt c h.boolean ((theta t).symm b)
        omega
      · intro b hb
        exact facts_terminal_south v x c carry digits h b b.property hb
    exact False.elim (hex 0 hstart)
  · have hex : ∀ b : Cell N, southWord c b ≠ 510 := by
      apply NativeFieldCycles2011.offset20_excludes_510 (theta t) (southWord c)
        (fun b => c (((theta t b : Cell N) : ZMod (N * 2011)) + 940) +
          2*c (((theta t b : Cell N) : ZMod (N * 2011)) + 941))
      · intro b
        exact offset20_error_le_two c t b (hcount (theta t b) (theta t b).property)
      · intro b
        have hh := offset20_word c h.boolean t b hr (hcopy b).1
        omega
    exact False.elim (hex 0 hstart)

/-- Fractional and whole-field alignment combine at the actual cell bit
length47*2011. This is a divisibility result about the original rank shift. -/
theorem facts_cell_aligned (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) % (47 * 2011) = 0 := by
  have hf := (facts_count_phase v x c carry digits h).2
  have hw := facts_whole_field v x c carry digits h
  omega

/-- The same polynomial-window witnesses, augmented by the derived
alignment. No replacement or resampling of the represented word occurs. -/
def AlignedWindow (v : Fin 14 → ℤ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ x : Fin 31 → ℕ, ∃ c carry digits : ZMod (N * 2011) → ℕ,
    Facts v N x c carry digits ∧
    ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47 * (N * 2011)) % (47 * 2011) = 0

theorem polynomial_zero_aligned_window (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, AlignedWindow v N hN := by
  obtain ⟨N, hN, hwin⟩ := polynomial_zero_window v hv hz
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨x, c, carry, digits, h⟩ := hwin
  exact ⟨N, hN, x, c, carry, digits, h, facts_cell_aligned v x c carry digits h⟩

end DiophantineConsistency.CurrentWholeField2011
