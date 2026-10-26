import DiophantineConsistency.CurrentWholeField2011
import DiophantineConsistency.CurrentAdjacency2011
import DiophantineConsistency.WangTiles942Language
import DiophantineConsistency.CurrentCellCycle2011

/-!
# Every aligned cell of the actual polynomial window is occupied

The forced Start supplies the first selected tile. The actual horizontal
copies transfer the positive West complement of an occupied cell to the
East word of its successor, excluding the decoded empty case there. The
spatial cycle then covers every aligned cell of the same original word.
No occupation, unique Start, marker value or tableau is supplied.
-/

namespace DiophantineConsistency.CurrentOccupation2011

open CurrentPolynomialWindow2011 CurrentCellLabels2011 CurrentDecodedWindow2011
  CurrentWholeField2011 CurrentCellTranslation2011 CurrentAdjacency2011
  WangTiles942
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

/-- The actual complemented West block, before any tile interpretation. -/
def westWord (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : ℕ :=
  binaryWord (fun j => c (b + ((978+j : ℕ) : ZMod (N * 2011)))) 8

/-- The actual complemented East block. -/
def eastWord (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : ℕ :=
  binaryWord (fun j => c (b + ((969+j : ℕ) : ZMod (N * 2011)))) 8

/-- Exactly one actual abstract tile is selected; every other selector is zero. -/
def Occupied (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011)) : Prop :=
  ∃ i : Fin 942, Selected (selectorValue c b) i

omit [NeZero (N * 2011)] in
/-- Aggregation of the eight physical copy equalities does not need labels. -/
theorem horizontal_words (c : ZMod (N * 2011) → ℕ) (b : ZMod (N * 2011))
    (hbits : ∀ j : Fin 8,
      c (b + ((969+j.val : ℕ) : ZMod (N * 2011))) =
      c (previousCell b + ((978+j.val : ℕ) : ZMod (N * 2011)))) :
    eastWord c b = westWord c (previousCell b) := by
  unfold eastWord westWord binaryWord
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun a : ℕ => 2^j*a) (hbits ⟨j, Finset.mem_range.mp hj⟩)

/-- Alignment and the horizontal copies are both derived from the original Facts. -/
theorem facts_horizontal_words (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    eastWord c b = westWord c (previousCell b) := by
  exact horizontal_words c b
    (facts_adjacency v x c carry digits h
      (facts_whole_field v x c carry digits h) b hb).2.2.1

omit [NeZero (N * 2011)] in
/-- Every selected actual tile has positive West complement. This uses the
proved strict horizontal color bound, not the weaker eight-bit bound. -/
theorem occupied_west_positive (c carry : ZMod (N * 2011) → ℕ) (W : ℕ)
    (hc : ∀ k, c k ≤ 1) (b : ZMod (N * 2011))
    (hd : CellDecoded c carry W b) (ho : Occupied c b) : 0 < westWord c b := by
  obtain ⟨i, hi⟩ := ho
  have hw := hd.word_of_selected i hi.1
  have hl := (labels_of_word c b hc i hw).1
  change westWord c b = 255 - (tile i).west at hl
  rw [hl]
  exact (WangTiles942Language.complemented_horizontal_positive i).1

/-- The known origin selector is the actual abstract Start tile0. -/
theorem facts_start_selected (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    Selected (selectorValue c 0) (0 : Fin 942) := by
  have hi : selectorValue c 0 0 = 1 := by
    simpa only [selectorValue, physicalPosition_zero, Nat.cast_zero, zero_add] using h.origin
  have hd := (facts_decode_cell v x c carry digits h 0 (by simp)).1
  obtain ⟨hz, _, _⟩ | ⟨i, hs, _, _⟩ := hd
  · have hh := hz 0
    omega
  · have he : (0 : Fin 942) = i := hs.unique 0 hi
    simpa only [he] using hs

/-- One occupied cell forces occupation at its actual spatial successor. -/
theorem facts_next_occupied (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : Cell N) (ho : Occupied c b) :
    Occupied c (CurrentCellCycle2011.next b : Cell N) := by
  have hbdecode := (facts_decode_cell v x c carry digits h b b.property).1
  have hp := occupied_west_positive c carry _ h.boolean b hbdecode ho
  have hcopy := facts_horizontal_words v x c carry digits h
    (CurrentCellCycle2011.next b : Cell N) (CurrentCellCycle2011.next b).property
  have hprevious : previousCell ((CurrentCellCycle2011.next b : Cell N) : ZMod (N * 2011)) =
      (b : ZMod (N * 2011)) := by
    rw [CurrentCellCycle2011.coe_next]
    unfold previousCell
    ring
  rw [hprevious] at hcopy
  have hnext := (facts_decode_cell v x c carry digits h
    (CurrentCellCycle2011.next b : Cell N) (CurrentCellCycle2011.next b).property).1
  obtain ⟨_, hzero, _⟩ | ⟨i, hs, _, _⟩ := hnext
  · have he := (labels_of_zero c (CurrentCellCycle2011.next b : Cell N) hzero).2.2.1
    change eastWord c (CurrentCellCycle2011.next b : Cell N) = 0 at he
    omega
  · exact ⟨i, hs⟩

/-- Every aligned cell is occupied on the same original Boolean word. -/
theorem facts_occupied (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    ∀ b : Cell N, Occupied c b := by
  apply CurrentCellCycle2011.propagate (fun b : Cell N => Occupied c b)
  · exact ⟨0, facts_start_selected v x c carry digits h⟩
  · exact facts_next_occupied v x c carry digits h

/-- The literal count is exactly one, not merely at most one. -/
theorem facts_selectorCount_eq_one (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    CurrentClause2011.selectorCount c b = 1 := by
  obtain ⟨i, hs⟩ := facts_occupied v x c carry digits h (⟨b, hb⟩ : Cell N)
  change (∑ j : Fin 942, selectorValue c b j) = 1
  simpa only [one_mul] using hs.weighted_sum (fun _ => 1)

/-- The original arithmetic witnesses augmented by all-cell occupation. -/
def OccupiedWindow (v : Fin 14 → ℤ) (N : ℕ) (hN : 0 < N) : Prop :=
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  ∃ x : Fin 31 → ℕ, ∃ c carry digits : ZMod (N * 2011) → ℕ,
    Facts v N x c carry digits ∧ ∀ b : Cell N, Occupied c b

theorem polynomial_zero_occupied_window (v : Fin 14 → ℤ) (hv : ∀ j, 0 < v j)
    (hz : MvPolynomial.eval v polynomial = 0) :
    ∃ N, ∃ hN : 0 < N, OccupiedWindow v N hN := by
  obtain ⟨N, hN, hwin⟩ := polynomial_zero_window v hv hz
  letI : NeZero (N * 2011) := ⟨Nat.ne_of_gt (Nat.mul_pos hN (by decide))⟩
  obtain ⟨x, c, carry, digits, h⟩ := hwin
  exact ⟨N, hN, x, c, carry, digits, h, facts_occupied v x c carry digits h⟩

end DiophantineConsistency.CurrentOccupation2011
