import DiophantineConsistency.ArithmeticTilingTable

/-! **K2b — operating and finishing rows of the constructed tiling**, in every
model of IΣ1 (construction spec §4 W2, `runTile`/`finishTile`).

For a configuration code `c` with absolute head column `H`, `rowIdx c H X` is
the table index of the tile at column `X`: a plain pass tile carrying the tape
bit, the transition tile at the head, and the receiver of its rail at the next
head column; when `c` is halted every tile is a pass tile (the head pass tile
`431+b` at the head). `finIdx c H X` is the finishing row of a halted
configuration.

Exported row laws (`first c ≤ 215`, columns arbitrary internal elements):
* `row_north` — north colour = `colorV c H X`, the row colour of `c`;
* `row_south_live` — for an operating `c` and `H ≥ 1`, south colour =
  `colorV (stepValue c) (hstep c H) X`, the row colour of the next
  configuration at the next head column; `row_south_halted` — south = north;
* `row_east` — horizontal matching `east(X) = west(X+1)` at every column;
* `row_west_one` (`H ≥ 2`) and `row_east_right` (`H < X`) — blank side
  colours away from the head, used at the seam columns;
* the corresponding `fin_*` laws and index bounds `row_lt`, `fin_lt`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticTilingRows
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticWangTable ArithmeticWangPlane ArithmeticRunTrace
  ArithmeticTilingTable

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Functions from first-order graphs -/

theorem fun1_of_rel {f : V → V} {R : V → V → Prop}
    (hR : 𝚺₁.Definable (fun v : Fin 2 → V => R (v 0) (v 1)))
    (h : ∀ y a, R y a ↔ y = f a) : 𝚺₁-Function₁ f :=
  hR.of_iff fun v => (h (v 0) (v 1)).symm

theorem fun2_of_rel {f : V → V → V} {R : V → V → V → Prop}
    (hR : 𝚺₁.Definable (fun v : Fin 3 → V => R (v 0) (v 1) (v 2)))
    (h : ∀ y a b, R y a b ↔ y = f a b) : 𝚺₁-Function₂ f :=
  hR.of_iff fun v => (h (v 0) (v 1) (v 2)).symm

theorem fun3_of_rel {f : V → V → V → V} {R : V → V → V → V → Prop}
    (hR : 𝚺₁.Definable (fun v : Fin 4 → V => R (v 0) (v 1) (v 2) (v 3)))
    (h : ∀ y a b c, R y a b c ↔ y = f a b c) : 𝚺₁-Function₃ f :=
  hR.of_iff fun v => (h (v 0) (v 1) (v 2) (v 3)).symm

/-! ## Tape bits, head and receiver indices -/

/-- The tape bit of configuration `c` at column `X` when the head is at `H`. -/
def bitAt (c H X : V) : V := tb (first (second c)) (second (second c)) H X

def BitRel (y c H X : V) : Prop :=
  (H ≤ X ∧ y = fbit (second (second c)) (X - H)) ∨
  (X < H ∧ y = fbit (first (second c)) (H - X - 1))

theorem bitRel_iff (y c H X : V) : BitRel y c H X ↔ y = bitAt c H X := by
  unfold BitRel bitAt tb
  by_cases h : H ≤ X
  · simp [h]
  · simp [h, lt_of_not_ge h]

instance bitAt_definable : 𝚺₁-Function₃ (bitAt : V → V → V → V) :=
  fun3_of_rel (by unfold BitRel; definability) bitRel_iff

theorem bitAt_le (c H X : V) : bitAt c H X ≤ 1 := tb_le _ _ _ _

theorem bitAt_head (c H : V) : bitAt c H H = second (second c) % 2 := tb_head _ _ _

theorem colorV_eq (c H X : V) :
    colorV c H X = if X = H then hcV (first c) (second (second c) % 2) else bitAt c H X := rfl

/-- The transition tile of an operating configuration. -/
def headIdx (c : V) : V := 2 * first c + second (second c) % 2 - 1

instance headIdx_definable : 𝚺₁-Function₁ (headIdx : V → V) := by
  unfold headIdx; definability

/-- The receiver of the head's rail, receiving bit `b`. -/
def rcvIdx (c b : V) : V := 423 + 2 * (eastC (headIdx c) + westC (headIdx c)) + b

instance rcvIdx_definable : 𝚺₁-Function₂ (rcvIdx : V → V → V) := by
  unfold rcvIdx; definability

/-! ## Operating rows -/

/-- The tile index at column `X` of the row of configuration `c`, head `H`. -/
def rowIdx (c H X : V) : V :=
  if first c = 0 then (if X = H then 431 + bitAt c H X else 433 + bitAt c H X)
  else if X = H then headIdx c
  else if (X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0) then
    rcvIdx c (bitAt c H X)
  else 433 + bitAt c H X

def RowRel (y c H X : V) : Prop :=
  (first c = 0 ∧ X = H ∧ y = 431 + bitAt c H X) ∨
  (first c = 0 ∧ X ≠ H ∧ y = 433 + bitAt c H X) ∨
  (first c ≠ 0 ∧ X = H ∧ y = headIdx c) ∨
  (first c ≠ 0 ∧ X ≠ H ∧ ((X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨
    (X + 1 = H ∧ westC (headIdx c) ≠ 0)) ∧ y = rcvIdx c (bitAt c H X)) ∨
  (first c ≠ 0 ∧ X ≠ H ∧ (X ≠ H + 1 ∨ eastC (headIdx c) = 0) ∧
    (X + 1 ≠ H ∨ westC (headIdx c) = 0) ∧ y = 433 + bitAt c H X)

theorem rowRel_iff (y c H X : V) : RowRel y c H X ↔ y = rowIdx c H X := by
  unfold RowRel rowIdx
  by_cases h0 : first c = 0
  · by_cases hX : X = H <;> simp [h0, hX]
  · by_cases hX : X = H
    · simp [h0, hX]
    · by_cases hr : (X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0)
      · rcases hr with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h0, hX, h1, h2]
      · have hn := not_or.mp hr
        simp only [not_and_or, not_not] at hn
        simp [h0, hX, hr, hn.1, hn.2]

instance rowIdx_definable : 𝚺₁-Function₃ (rowIdx : V → V → V → V) :=
  fun3_of_rel (by unfold RowRel; definability) rowRel_iff

theorem row_halted {c H X : V} (h0 : first c = 0) :
    rowIdx c H X = if X = H then 431 + bitAt c H X else 433 + bitAt c H X := by
  rw [rowIdx, if_pos h0]

theorem row_head {c H : V} (h0 : first c ≠ 0) : rowIdx c H H = headIdx c := by
  rw [rowIdx, if_neg h0, if_pos rfl]

theorem row_rcv {c H X : V} (h0 : first c ≠ 0) (hX : X ≠ H)
    (hr : (X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0)) :
    rowIdx c H X = rcvIdx c (bitAt c H X) := by
  rw [rowIdx, if_neg h0, if_neg hX, if_pos hr]

theorem row_pass {c H X : V} (h0 : first c ≠ 0) (hX : X ≠ H)
    (hr : ¬ ((X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0))) :
    rowIdx c H X = 433 + bitAt c H X := by
  rw [rowIdx, if_neg h0, if_neg hX, if_neg hr]

/-- The head tile and its receivers of an operating configuration. -/
theorem head_facts {c : V} (h0 : first c ≠ 0) (hc : first c ≤ 215) :
    headIdx c < 942 ∧ northC (headIdx c) = 2 * first c + second (second c) % 2 ∧
    ∀ b : V, b ≤ 1 → rcvIdx c b < 942 ∧ westC (rcvIdx c b) = eastC (headIdx c) ∧
      northC (rcvIdx c b) = b ∧ eastC (rcvIdx c b) = westC (headIdx c) :=
  head_receiver h0 hc (bit_le _)

/-- The action of an operating row: written bit, direction, side colours of
the head and the south colour of the receiver. -/
theorem live_row {c : V} (h0 : first c ≠ 0) (hc : first c ≤ 215) :
    ∃ st' d w : V, st' ≤ 215 ∧ d ≤ 1 ∧ w ≤ 1 ∧ act c = 1 + 4 * st' + 2 * d + w ∧
      southC (headIdx c) = w ∧
      (∀ b : V, b ≤ 1 → southC (rcvIdx c b) = hcV st' b) ∧
      (d = 1 → westC (headIdx c) = 0 ∧ eastC (headIdx c) ≠ 0) ∧
      (d = 0 → eastC (headIdx c) = 0 ∧ westC (headIdx c) ≠ 0) := by
  obtain ⟨hi, hn, hr⟩ := head_facts h0 hc
  obtain ⟨st', d, w, hst', hd, hw, hA, hs, h1, h2⟩ := head_step hi h0 hc (bit_le _) hn
  refine ⟨st', d, w, hst', hd, hw, hA, hs, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨hlt, hwest, hnorth, heast⟩ := hr b hb
    rcases bit_cases' hd with rfl | rfl
    · obtain ⟨-, -, hrecv⟩ := h2 rfl
      rw [hrecv _ hlt (by rw [hnorth]; exact hb) heast, hnorth]
    · obtain ⟨-, -, hrecv⟩ := h1 rfl
      rw [hrecv _ hlt (by rw [hnorth]; exact hb) hwest, hnorth]
  · intro hd1
    obtain ⟨hw0, he, -⟩ := h1 hd1
    exact ⟨hw0, ne_of_gt (lt_of_lt_of_le (by norm_num) he)⟩
  · intro hd0
    obtain ⟨he0, hw', -⟩ := h2 hd0
    exact ⟨he0, ne_of_gt (lt_of_lt_of_le (by norm_num) hw')⟩

theorem row_lt {c H X : V} (hc : first c ≤ 215) : rowIdx c H X < 942 := by
  have hb := bitAt_le c H X
  unfold rowIdx
  by_cases h0 : first c = 0
  · rw [if_pos h0]; split
    · exact halt_lt hb
    · exact pass_lt hb
  · rw [if_neg h0]
    obtain ⟨hi, -, hr⟩ := head_facts h0 hc
    split
    · exact hi
    · split
      · exact (hr _ hb).1
      · exact pass_lt hb

theorem row_north {c H X : V} (hc : first c ≤ 215) :
    northC (rowIdx c H X) = colorV c H X := by
  have hb := bitAt_le c H X
  rw [colorV_eq]
  by_cases h0 : first c = 0
  · rw [row_halted h0]
    by_cases hX : X = H
    · subst hX
      rw [if_pos rfl, if_pos rfl, (halt_colours hb).north, h0, hcV, if_pos rfl, bitAt_head]
    · rw [if_neg hX, if_neg hX, (pass_colours hb).north]
  · obtain ⟨-, hn, hr⟩ := head_facts h0 hc
    by_cases hX : X = H
    · subst hX
      rw [row_head h0, if_pos rfl, hn, hcV, if_neg h0]
    · rw [if_neg hX]
      by_cases hrc : (X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0)
      · rw [row_rcv h0 hX hrc]; exact (hr _ hb).2.2.1
      · rw [row_pass h0 hX hrc]; exact (pass_colours hb).north

theorem row_south_halted {c H X : V} (h0 : first c = 0) :
    southC (rowIdx c H X) = colorV c H X := by
  have hb := bitAt_le c H X
  rw [colorV_eq, row_halted h0]
  by_cases hX : X = H
  · subst hX
    rw [if_pos rfl, if_pos rfl, (halt_colours hb).south, h0, hcV, if_pos rfl, bitAt_head]
  · rw [if_neg hX, if_neg hX, (pass_colours hb).south]

theorem hstep_live {c H st' d w : V} (hd : d ≤ 1) (hw : w ≤ 1)
    (hA : act c = 1 + 4 * st' + 2 * d + w) :
    hstep c H = if d = 0 then H - 1 else H + 1 := by
  have hpos : (0 : V) < 1 + 4 * st' + 2 * d + w := by positivity
  rw [hstep, hA, if_neg (ne_of_gt hpos), action_fields hd hw]

/-- **Row step.** The south colours of an operating row are the row colours of
the next configuration at the next head column. -/
theorem row_south_live {c H X : V} (h0 : first c ≠ 0) (hc : first c ≤ 215) (hH : 1 ≤ H) :
    southC (rowIdx c H X) = colorV (ArithmeticMachineStep215.stepValue c) (hstep c H) X := by
  obtain ⟨st', d, w, -, hd, hw, hA, hs, hrs, h1, h2⟩ := live_row h0 hc
  have hb := bitAt_le c H X
  rw [hstep_live hd hw hA, step_apply c st' d w hd hw hA]
  rcases bit_cases' hd with rfl | rfl
  · -- left move
    obtain ⟨he0, hw0⟩ := h2 rfl
    obtain ⟨G, rfl⟩ : ∃ G, H = G + 1 := ⟨H - 1, (tsub_add_cancel_of_le hH).symm⟩
    rw [if_pos rfl, if_pos rfl, add_tsub_cancel_right]
    simp only [colorV, first_cantor, second_cantor]
    by_cases hX : X = G + 1
    · rw [hX, row_head h0, hs, if_neg (show ¬ (G + 1 = G) by simp),
        tb_left_old (first (second c)) (second (second c)) w G hw]
    · by_cases hXG : X = G
      · rw [hXG] at hX ⊢
        rw [row_rcv h0 hX (Or.inr ⟨rfl, hw0⟩), hrs _ (bitAt_le _ _ _), if_pos rfl, bitAt,
          ← tb_left (first (second c)) (second (second c)) w G G hw hX, tb_head]
      · have hn : ¬ ((X = G + 1 + 1 ∧ eastC (headIdx c) ≠ 0) ∨
            (X + 1 = G + 1 ∧ westC (headIdx c) ≠ 0)) := by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact h he0
          · exact hXG (add_right_cancel h)
        rw [row_pass h0 hX hn, (pass_colours hb).south, if_neg hXG, bitAt]
        exact (tb_left (first (second c)) (second (second c)) w G X hw hX).symm
  · -- right move
    obtain ⟨hw0, he0⟩ := h1 rfl
    rw [if_neg _root_.one_ne_zero, if_neg _root_.one_ne_zero]
    simp only [colorV, first_cantor, second_cantor]
    by_cases hX : X = H
    · rw [hX, row_head h0, hs, if_neg (show ¬ (H = H + 1) by simp),
        tb_right_old (first (second c)) (second (second c)) w H hw]
    · by_cases hX1 : X = H + 1
      · rw [hX1] at hX ⊢
        rw [row_rcv h0 hX (Or.inl ⟨rfl, he0⟩), hrs _ (bitAt_le _ _ _), if_pos rfl, bitAt,
          ← tb_right (first (second c)) (second (second c)) w H (H + 1) hw hX, tb_head]
      · have hn : ¬ ((X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0)) := by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact hX1 h
          · exact h hw0
        rw [row_pass h0 hX hn, (pass_colours hb).south, if_neg hX1, bitAt]
        exact (tb_right (first (second c)) (second (second c)) w H X hw hX).symm

/-- Side colours of an operating row. -/
theorem live_sides {c H : V} (h0 : first c ≠ 0) (hc : first c ≤ 215) :
    (∀ X, westC (rowIdx c H X) = (if X = H + 1 then eastC (headIdx c) else 0) ∧
      eastC (rowIdx c H X) = (if X = H then eastC (headIdx c) else 0)) ∨
    (∀ X, westC (rowIdx c H X) = (if X = H then westC (headIdx c) else 0) ∧
      eastC (rowIdx c H X) = (if X + 1 = H then westC (headIdx c) else 0)) := by
  obtain ⟨st', d, w, -, hd, -, -, -, -, h1, h2⟩ := live_row h0 hc
  obtain ⟨-, -, hr⟩ := head_facts h0 hc
  rcases bit_cases' hd with rfl | rfl
  · obtain ⟨he0, hw0⟩ := h2 rfl
    right
    intro X
    have hb := bitAt_le c H X
    by_cases hX : X = H
    · rw [hX, row_head h0, if_pos rfl, if_neg (show ¬ (H + 1 = H) by simp), he0]
      exact ⟨rfl, rfl⟩
    · by_cases hX1 : X + 1 = H
      · rw [row_rcv h0 hX (Or.inr ⟨hX1, hw0⟩), if_neg hX, if_pos hX1, (hr _ hb).2.1,
          (hr _ hb).2.2.2, he0]
        exact ⟨rfl, rfl⟩
      · have hn : ¬ ((X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0)) := by
          rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact h he0
          · exact hX1 h
        rw [row_pass h0 hX hn, if_neg hX, if_neg hX1,
          (pass_colours hb).west, (pass_colours hb).east]
        exact ⟨rfl, rfl⟩
  · obtain ⟨hw0, he0⟩ := h1 rfl
    left
    intro X
    have hb := bitAt_le c H X
    by_cases hX : X = H
    · rw [hX, row_head h0, if_pos rfl, if_neg (show ¬ (H = H + 1) by simp), hw0]
      exact ⟨rfl, rfl⟩
    · by_cases hX1 : X = H + 1
      · rw [row_rcv h0 hX (Or.inl ⟨hX1, he0⟩), if_neg hX, if_pos hX1, (hr _ hb).2.1,
          (hr _ hb).2.2.2, hw0]
        exact ⟨rfl, rfl⟩
      · have hn : ¬ ((X = H + 1 ∧ eastC (headIdx c) ≠ 0) ∨ (X + 1 = H ∧ westC (headIdx c) ≠ 0)) := by
          rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact hX1 h
          · exact h hw0
        rw [row_pass h0 hX hn, if_neg hX, if_neg hX1,
          (pass_colours hb).west, (pass_colours hb).east]
        exact ⟨rfl, rfl⟩

theorem halted_sides {c H X : V} (h0 : first c = 0) :
    westC (rowIdx c H X) = 0 ∧ eastC (rowIdx c H X) = 0 := by
  have hb := bitAt_le c H X
  rw [row_halted h0]
  split
  · exact ⟨(halt_colours hb).west, (halt_colours hb).east⟩
  · exact ⟨(pass_colours hb).west, (pass_colours hb).east⟩

/-- Horizontal matching inside a row. -/
theorem row_east {c H X : V} (hc : first c ≤ 215) :
    eastC (rowIdx c H X) = westC (rowIdx c H (X + 1)) := by
  by_cases h0 : first c = 0
  · rw [(halted_sides h0).2, (halted_sides h0).1]
  · rcases live_sides (H := H) h0 hc with h | h
    · rw [(h X).2, (h (X + 1)).1]
      by_cases hX : X = H
      · rw [if_pos hX, if_pos (by rw [hX])]
      · rw [if_neg hX, if_neg (fun e => hX (add_right_cancel e))]
    · rw [(h X).2, (h (X + 1)).1]

theorem row_west_one {c H : V} (hc : first c ≤ 215) (hH : 2 ≤ H) :
    westC (rowIdx c H 1) = 0 := by
  by_cases h0 : first c = 0
  · exact (halted_sides h0).1
  · have h1 : (1 : V) ≠ H + 1 := by
      intro e; have : (2 : V) ≤ 1 := by
        calc (2 : V) ≤ H := hH
          _ ≤ H + 1 := le_add_of_nonneg_right (Arithmetic.zero_le 1)
          _ = 1 := e.symm
      exact absurd this (by norm_num)
    have h2 : (1 : V) ≠ H := by
      intro e; rw [← e] at hH; exact absurd hH (by norm_num)
    rcases live_sides (H := H) h0 hc with h | h
    · rw [(h 1).1, if_neg h1]
    · rw [(h 1).1, if_neg h2]

theorem row_east_right {c H X : V} (hc : first c ≤ 215) (hX : H < X) :
    eastC (rowIdx c H X) = 0 := by
  by_cases h0 : first c = 0
  · exact (halted_sides h0).2
  · rcases live_sides (H := H) h0 hc with h | h
    · rw [(h X).2, if_neg (ne_of_gt hX)]
    · rw [(h X).2, if_neg]
      intro e
      have : X < H := by rw [← e]; exact lt_add_one X
      exact absurd (lt_trans hX this) (_root_.lt_irrefl _)

/-! ## The finishing row -/

/-- The finishing row of a halted configuration: south colour 438. -/
def finIdx (c H X : V) : V := if X = H then 925 + bitAt c H X else 923 + bitAt c H X

def FinRel (y c H X : V) : Prop :=
  (X = H ∧ y = 925 + bitAt c H X) ∨ (X ≠ H ∧ y = 923 + bitAt c H X)

theorem finRel_iff (y c H X : V) : FinRel y c H X ↔ y = finIdx c H X := by
  unfold FinRel finIdx
  by_cases hX : X = H <;> simp [hX]

instance finIdx_definable : 𝚺₁-Function₃ (finIdx : V → V → V → V) :=
  fun3_of_rel (by unfold FinRel; definability) finRel_iff

theorem fin_lt (c H X : V) : finIdx c H X < 942 := by
  have hb := bitAt_le c H X
  unfold finIdx; split
  · exact finish_head_lt hb
  · exact finish_lt hb

theorem fin_colours {c H X : V} (h0 : first c = 0) :
    westC (finIdx c H X) = 0 ∧ northC (finIdx c H X) = colorV c H X ∧
      eastC (finIdx c H X) = 0 ∧ southC (finIdx c H X) = 438 := by
  have hb := bitAt_le c H X
  rw [colorV_eq]
  unfold finIdx
  by_cases hX : X = H
  · subst hX
    rw [if_pos rfl, if_pos rfl, h0, hcV, if_pos rfl, bitAt_head]
    have h := finish_head_colours (bit_le (second (second c)))
    exact ⟨h.west, h.north, h.east, h.south⟩
  · rw [if_neg hX, if_neg hX]
    have h := finish_colours hb
    exact ⟨h.west, h.north, h.east, h.south⟩

end DiophantineConsistency.ArithmeticTilingRows
