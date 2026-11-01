import DiophantineConsistency.ArithmeticTilingRows

/-! **K2c — the band of the constructed tiling** (construction spec §4 W2),
in every model of IΣ1: the seam column `seamIdx`, the initializer row
`initIdx`, the reset row `resetIdx`, the full band `bandIdx T H X k` (rows
`1..H-3` from `ArithmeticTilingRows.rowIdx` of the represented run, row `H-2`
the finishing row), its helical quotient `cellOf` and the word `word`, with
their Σ1 definability (graphs as explicit case relations), and the local
colour facts of the fixed rows (`reset_south_init`, `init_east`,
`init_south_row1`, `seam_vertical`). `ArithmeticTilingWord` proves the
marked-word property from these. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.ArithmeticTilingBand
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCantor ArithmeticWangTable ArithmeticWangPlane ArithmeticRunTrace
  ArithmeticTilingTable ArithmeticTilingRows
open ArithmeticMachineRun215 (run run_succ)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## The band -/

/-- Seam column: `⟨ec(k-1)², 437, ec(k), 437⟩` with `ec 0 = 2`, `ec (H-1) = 1`. -/
def seamIdx (H k : V) : V :=
  if k = 0 then 938 else if k = 1 then 939 else if k + 1 = H then 934 else 933

/-- Initializer row (row `0`), Start at column `L`. -/
def initIdx (L X : V) : V :=
  if X < L then 927 else if X = L then 0 else if X = L + 1 then 928 else 929

/-- Reset row (row `H-1`); its south colours are the initializer's norths. -/
def resetIdx (L X : V) : V := if X < L then 930 else if X = L then 931 else 932

def bandIdx (T H X k : V) : V :=
  if X = 0 then seamIdx H k
  else if k = 0 then initIdx (T + 2) X
  else if k + 1 = H then resetIdx (T + 2) X
  else if k + 2 = H then finIdx (run k) (hd (T + 2) k) X
  else rowIdx (run k) (hd (T + 2) k) X

/-- The helical quotient of the band. -/
def cellOf (T w H y : V) : V := bandIdx T H (y % w) (y / w % H)

/-- **The constructed tiling word** on `N = w·H` cells. -/
def word (T w H z : V) : V := cellOf T w H (T + 2 + w * H - z)

/-! ## Definability -/

def SeamRel (y H k : V) : Prop :=
  (k = 0 ∧ y = 938) ∨ (k ≠ 0 ∧ k = 1 ∧ y = 939) ∨ (k ≠ 0 ∧ k ≠ 1 ∧ k + 1 = H ∧ y = 934) ∨
  (k ≠ 0 ∧ k ≠ 1 ∧ k + 1 ≠ H ∧ y = 933)

theorem seamRel_iff (y H k : V) : SeamRel y H k ↔ y = seamIdx H k := by
  unfold SeamRel seamIdx
  split_ifs <;> simp_all

instance seamIdx_definable : 𝚺₁-Function₂ (seamIdx : V → V → V) :=
  fun2_of_rel (by unfold SeamRel; definability) seamRel_iff

def InitRel (y L X : V) : Prop :=
  (X < L ∧ y = 927) ∨ (X = L ∧ y = 0) ∨ (X = L + 1 ∧ y = 928) ∨ (L + 1 < X ∧ y = 929)

theorem initRel_iff (y L X : V) : InitRel y L X ↔ y = initIdx L X := by
  unfold InitRel initIdx
  rcases lt_trichotomy X L with h | rfl | h
  · simp [h, ne_of_lt h, not_lt.mpr (le_of_lt (lt_trans h (lt_add_one L))),
      ne_of_lt (lt_trans h (lt_add_one L))]
  · simp
  · have h1 : ¬ X < L := not_lt.mpr h.le
    have h2 : X ≠ L := ne_of_gt h
    rcases eq_or_lt_of_le (lt_iff_succ_le.mp h) with e | e
    · subst e; simp
    · simp [h1, h2, ne_of_gt e, e]

instance initIdx_definable : 𝚺₁-Function₂ (initIdx : V → V → V) :=
  fun2_of_rel (by unfold InitRel; definability) initRel_iff

def ResetRel (y L X : V) : Prop := (X < L ∧ y = 930) ∨ (X = L ∧ y = 931) ∨ (L < X ∧ y = 932)

theorem resetRel_iff (y L X : V) : ResetRel y L X ↔ y = resetIdx L X := by
  unfold ResetRel resetIdx
  rcases lt_trichotomy X L with h | rfl | h
  · simp [h, ne_of_lt h, not_lt.mpr h.le]
  · simp
  · simp [h, ne_of_gt h, not_lt.mpr h.le]

instance resetIdx_definable : 𝚺₁-Function₂ (resetIdx : V → V → V) :=
  fun2_of_rel (by unfold ResetRel; definability) resetRel_iff

def BandRel (T H y X k : V) : Prop :=
  (X = 0 ∧ y = seamIdx H k) ∨ (X ≠ 0 ∧ k = 0 ∧ y = initIdx (T + 2) X) ∨
  (X ≠ 0 ∧ k ≠ 0 ∧ k + 1 = H ∧ y = resetIdx (T + 2) X) ∨
  (X ≠ 0 ∧ k ≠ 0 ∧ k + 1 ≠ H ∧ k + 2 = H ∧ y = finIdx (run k) (hd (T + 2) k) X) ∨
  (X ≠ 0 ∧ k ≠ 0 ∧ k + 1 ≠ H ∧ k + 2 ≠ H ∧ y = rowIdx (run k) (hd (T + 2) k) X)

theorem bandRel_iff (T H y X k : V) : BandRel T H y X k ↔ y = bandIdx T H X k := by
  unfold BandRel bandIdx
  split_ifs <;> simp_all

instance bandIdx_definable (T H : V) : 𝚺₁-Function₂ (bandIdx T H) :=
  fun2_of_rel (R := BandRel T H) (by unfold BandRel; definability) (bandRel_iff T H)

instance cellOf_definable (T w H : V) : 𝚺₁-Function₁ (cellOf T w H) := by
  unfold cellOf; definability

instance word_definable (T w H : V) : 𝚺₁-Function₁ (word T w H) := by
  unfold word; definability

/-! ## Local colour facts of the fixed rows -/

section fixed
variable {L X : V}

theorem init_lt (h : X < L) : initIdx L X = 927 := by rw [initIdx, if_pos h]
theorem init_eq : initIdx L L = 0 := by simp [initIdx]
theorem init_succ : initIdx L (L + 1) = 928 := by simp [initIdx]
theorem init_gt (h : L + 1 < X) : initIdx L X = 929 := by
  have h1 : L < X := lt_trans (lt_add_one L) h
  rw [initIdx, if_neg (not_lt.mpr h1.le), if_neg (ne_of_gt h1), if_neg (ne_of_gt h)]

theorem reset_south_init (L X : V) : southC (resetIdx L X) = northC (initIdx L X) := by
  rcases lt_trichotomy X L with h | rfl | h
  · rw [resetIdx, if_pos h, init_lt h, c930.south, c927.north]
  · rw [resetIdx, if_neg (_root_.lt_irrefl _), if_pos rfl, init_eq, c931.south, c0.north]
  · have hn : ¬ X < L := not_lt.mpr h.le
    rw [resetIdx, if_neg hn, if_neg (ne_of_gt h), c932.south]
    rcases eq_or_lt_of_le (lt_iff_succ_le.mp h) with e | e
    · rw [← e, init_succ, c928.north]
    · rw [init_gt e, c929.north]

theorem reset_sides (L X : V) : westC (resetIdx L X) = 1 ∧ eastC (resetIdx L X) = 1 := by
  unfold resetIdx
  split_ifs <;> simp only [c930.west, c930.east, c931.west, c931.east,
    c932.west, c932.east, true_and]

theorem init_east (hL : 1 ≤ L) (X : V) : eastC (initIdx L X) = westC (initIdx L (X + 1)) := by
  rcases lt_trichotomy (X + 1) L with h | h | h
  · rw [init_lt (lt_trans (lt_add_one X) h), init_lt h, c927.east, c927.west]
  · rw [init_lt (by rw [← h]; exact lt_add_one X), h, init_eq, c927.east, c0.west]
  · have hX : L ≤ X := lt_succ_iff_le.mp h
    rcases eq_or_lt_of_le hX with e | e
    · rw [← e, init_eq, init_succ, c0.east, c928.west]
    · rcases eq_or_lt_of_le (lt_iff_succ_le.mp e) with e' | e'
      · rw [← e', init_succ, init_gt (by rw [e']; exact lt_add_one X) , c928.east, c929.west]
      · rw [init_gt e', init_gt (lt_trans e' (lt_add_one X)), c929.east, c929.west]

theorem init_lt942 (L X : V) : initIdx L X < 942 := by
  unfold initIdx; repeat (first | split | norm_num)

theorem reset_lt942 (L X : V) : resetIdx L X < 942 := by
  unfold resetIdx; repeat (first | split | norm_num)

theorem seam_lt942 (H k : V) : seamIdx H k < 942 := by
  unfold seamIdx; repeat (first | split | norm_num)

theorem seam_vertical (H k k' : V) : southC (seamIdx H k) = northC (seamIdx H k') := by
  have hc (t : V) : southC (seamIdx H t) = 437 ∧ northC (seamIdx H t) = 437 := by
    unfold seamIdx
    split_ifs <;> simp only [c938.south, c939.south, c934.south, c933.south,
      c938.north, c939.north, c934.north, c933.north, true_and]
  exact (hc k).1.trans (hc k').2.symm

end fixed

theorem two_le_L (T : V) : (1 : V) ≤ T + 2 :=
  le_trans (by norm_num) (le_add_of_nonneg_left (Arithmetic.zero_le T))

theorem one_lt_H {H : V} (hH4 : 4 ≤ H) : (1 : V) + 2 < H := lt_of_lt_of_le (by norm_num) hH4

/-- Row `1` is the first operating row: the colours of `run 1` from head
column `L+1` are the initializer's south colours. -/
theorem init_south_row1 (L X : V) :
    southC (initIdx L X) = colorV (cantor 2 (cantor 1 0)) (L + 1) X := by
  simp only [colorV, first_cantor, second_cantor, tb]
  have h2 : (2 : V) ≠ 0 := by norm_num
  rcases lt_trichotomy X L with h | rfl | h
  · have hn1 : X ≠ L + 1 := ne_of_lt (lt_trans h (lt_add_one L))
    have hn2 : ¬ L + 1 ≤ X := not_le.mpr (lt_trans h (lt_add_one L))
    rw [init_lt h, c927.south, if_neg hn1, if_neg hn2]
    obtain ⟨j, hj⟩ : ∃ j, L + 1 - X - 1 = j + 1 := by
      refine ⟨L - X - 1, ?_⟩
      rw [tsub_right_comm, add_tsub_cancel_right,
        tsub_add_cancel_of_le (pos_iff_one_le.mp (tsub_pos_of_lt h))]
    have hb : fbit (1 : V) (j + 1) = 0 := by simpa using fbit_mul_two_add_one_mul (0 : V) j
    rw [hj, hb]
  · have hb : fbit (1 : V) 0 = 1 := by simpa using fbit_two_mul_add_one_zero_eq_one (0 : V)
    rw [init_eq, c0.south, if_neg (show ¬ (X = X + 1) by simp), if_neg (show ¬ (X + 1 ≤ X) by simp),
      show X + 1 - X - 1 = (0 : V) by simp, hb]
  · rcases eq_or_lt_of_le (lt_iff_succ_le.mp h) with e | e
    · rw [← e, init_succ, c928.south, if_pos rfl, hcV, if_neg h2, zero_mod]; norm_num
    · rw [init_gt e, c929.south, if_neg (ne_of_gt e), if_pos e.le, fbit_zero]

theorem mod_succ_mod {H K : V} (hH0 : 0 < H) : (K + 1) % H = (K % H + 1) % H := by
  conv_lhs => rw [← div_add_mod K H]
  rw [add_assoc, mod_mul_add' _ _ hH0]


end DiophantineConsistency.ArithmeticTilingBand
