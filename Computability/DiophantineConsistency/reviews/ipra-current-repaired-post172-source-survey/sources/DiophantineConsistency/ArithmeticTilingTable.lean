import DiophantineConsistency.ArithmeticRunTrace

/-! **K2a — the tile indices used by the constructed tiling word**, in every
model of IΣ1 (construction spec §4, the (a) tile facts).

The constructed band uses only these rows of the 942-tile table
(`WangTiles942.orderedRows`):

| index | tile `⟨W,N,E,S⟩` | role |
|---|---|---|
| `0` | `⟨2,435,3,1⟩` | Start |
| `j+1`, `j < 430` | transition of input `j = 2q+b` | operating head |
| `423+2r+b` | `⟨E,b,W,hc⟩` with `r = E+W` | receiver of the rail `r` |
| `431+b`, `433+b` | `⟨0,432+b,0,432+b⟩`, `⟨0,b,0,b⟩` | halted head / plain pass |
| `923+b`, `925+b` | `⟨0,b,0,438⟩`, `⟨0,432+b,0,438⟩` | finish row |
| `927, 928, 929` | `⟨2,434,2,0⟩, ⟨3,436,4,4⟩, ⟨4,436,4,0⟩` | initializer row |
| `930, 931, 932` | `⟨1,438,1,434+i⟩` | reset row |
| `933, 934, 938, 939` | `⟨0,437,0,437⟩, ⟨0,437,1,437⟩, ⟨1,437,2,437⟩, ⟨4,437,0,437⟩` | seams |

Every fact is read in ℕ from the definition of `orderedRows` (each row sits
at its own index by `row_indices_exact`; transition targets lie in their
direction's target list), without any table-wide evaluation, and transported
to an arbitrary model through the numeral lookups of `ArithmeticWangTable`. The
receiver fact is uniform: the receiver of the head tile `i` (rail on whichever
side is nonzero) has west colour `eastC i`, east colour `westC i` and north
colour equal to the bit it receives; its south colour is supplied by
`ArithmeticWangTable.head_step`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace DiophantineConsistency.ArithmeticTilingTable
open SetTheory.BusyBeaver SetTheory.BusyBeaver.ZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open WangTiles942 ArithmeticWangTable

/-! ## Standard facts, read structurally from the ordered table -/

/-- Every row of the ordered table sits at its own index. -/
theorem row_tile {row : ℕ × Tile} (h : row ∈ orderedRows) : row.1 < 942 ∧ tileN row.1 = row.2 := by
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  subst he
  have hl : i < 942 := by rw [ordered_count] at hi; exact hi
  have hidx : (orderedRows[i]'hi).1 = i := by
    have h2 := congrArg (fun l : List ℕ => l[i]?) row_indices_exact
    simpa [hi, hl] using h2
  rw [hidx]
  exact ⟨hl, by simp only [tileN, dif_pos hl, tile]⟩

theorem mem_transition (j : Fin 430) : transitionRow j ∈ orderedRows :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩))))

theorem mem_copy {row : ℕ × Tile} (h : row ∈ copyRows 1 ++ copyRows 0) : row ∈ orderedRows :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem mem_signal {row : ℕ × Tile} (h : row ∈ signalRows true ++ signalRows false) :
    row ∈ orderedRows :=
  List.mem_append_left _ (List.mem_append_right _ h)

theorem mem_tail {row : ℕ × Tile} (h : row ∈ tailRows) : row ∈ orderedRows :=
  List.mem_append_right _ h

theorem signal_row (d : Bool) {q b : ℕ} (hq : q ∈ targetList d) (hb : b < 2) :
    (423 + 2 * rail d q + b, (⟨d.toNat * rail d q, b, (1 - d.toNat) * rail d q, headColor q b⟩ : Tile))
      ∈ orderedRows := by
  apply mem_signal
  have hm : (423 + 2 * rail d q + b,
      (⟨d.toNat * rail d q, b, (1 - d.toNat) * rail d q, headColor q b⟩ : Tile)) ∈ signalRows d :=
    List.mem_flatMap.mpr ⟨q, hq, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩⟩
  cases d
  · exact List.mem_append_right _ hm
  · exact List.mem_append_left _ hm

theorem action_target_mem' (j : Fin 430) : (action j).2.2 ∈ targetList (action j).2.1 := by
  apply List.mem_toFinset.mp
  change (action j).2.2 ∈ targets (action j).2.1
  rw [targets_eq_cache]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨action j, List.mem_filter.mpr ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, by simp⟩, rfl⟩

/-- The transition tile of input `j` and the receiver of its rail with bit `b`:
the receiver has the head's side colours exchanged. -/
theorem trans_shape (j : Fin 430) (b : ℕ) (hb : b < 2) :
    ∃ E W : ℕ, tileN (j.val + 1) = ⟨W, j.val + 2, E, (action j).1.toNat⟩ ∧
      423 + 2 * (E + W) + b < 942 ∧
      tileN (423 + 2 * (E + W) + b) = ⟨E, b, W, headColor (action j).2.2 b⟩ := by
  have ht : tileN (j.val + 1) = (transitionRow j).2 := (row_tile (mem_transition j)).2
  have hq := action_target_mem' j
  have hn : headColor (j.val / 2) (j.val % 2) = j.val + 2 := by unfold headColor; omega
  rcases hd : (action j).2.1 with _ | _
  · rw [hd] at hq
    obtain ⟨hlt, hs⟩ := row_tile (signal_row false hq hb)
    refine ⟨0, rail false (action j).2.2, ?_, ?_, ?_⟩
    · rw [ht]; simp only [transitionRow, hd, Bool.toNat_false, hn]; simp
    · simpa using hlt
    · simpa using hs
  · rw [hd] at hq
    obtain ⟨hlt, hs⟩ := row_tile (signal_row true hq hb)
    refine ⟨rail true (action j).2.2, 0, ?_, ?_, ?_⟩
    · rw [ht]; simp only [transitionRow, hd, Bool.toNat_true, hn]; simp
    · simpa using hlt
    · simpa using hs

theorem tail_tile {m : ℕ} {t : Tile} (h : (m, t) ∈ tailRows) : tileN m = t :=
  (row_tile (mem_tail h)).2
theorem copy_tile {m : ℕ} {t : Tile} (h : (m, t) ∈ copyRows 1 ++ copyRows 0) : tileN m = t :=
  (row_tile (mem_copy h)).2

theorem t923 : tileN 923 = ⟨0,0,0,438⟩ := tail_tile (by decide)
theorem t924 : tileN 924 = ⟨0,1,0,438⟩ := tail_tile (by decide)
theorem t925 : tileN 925 = ⟨0,432,0,438⟩ := tail_tile (by decide)
theorem t926 : tileN 926 = ⟨0,433,0,438⟩ := tail_tile (by decide)
theorem t927 : tileN 927 = ⟨2,434,2,0⟩ := tail_tile (by decide)
theorem t928 : tileN 928 = ⟨3,436,4,4⟩ := tail_tile (by decide)
theorem t929 : tileN 929 = ⟨4,436,4,0⟩ := tail_tile (by decide)
theorem t930 : tileN 930 = ⟨1,438,1,434⟩ := tail_tile (by decide)
theorem t931 : tileN 931 = ⟨1,438,1,435⟩ := tail_tile (by decide)
theorem t932 : tileN 932 = ⟨1,438,1,436⟩ := tail_tile (by decide)
theorem t933 : tileN 933 = ⟨0,437,0,437⟩ := tail_tile (by decide)
theorem t934 : tileN 934 = ⟨0,437,1,437⟩ := tail_tile (by decide)
theorem t938 : tileN 938 = ⟨1,437,2,437⟩ := tail_tile (by decide)
theorem t939 : tileN 939 = ⟨4,437,0,437⟩ := tail_tile (by decide)
theorem t431 : tileN 431 = ⟨0,432,0,432⟩ := copy_tile (by decide)
theorem t432 : tileN 432 = ⟨0,433,0,433⟩ := copy_tile (by decide)
theorem t433 : tileN 433 = ⟨0,0,0,0⟩ := copy_tile (by decide)
theorem t434 : tileN 434 = ⟨0,1,0,1⟩ := copy_tile (by decide)

/-! ## Transport -/

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The four colours of a standard index, as internal numerals. -/
structure Colours (i w n e s : V) : Prop where
  west : westC i = w
  north : northC i = n
  east : eastC i = e
  south : southC i = s

theorem colours_of {m : ℕ} {t : Tile} (h : tileN m = t) :
    Colours (m : V) (t.west : V) (t.north : V) (t.east : V) (t.south : V) :=
  ⟨by rw [westC_cast, h], by rw [northC_cast, h], by rw [eastC_cast, h], by rw [southC_cast, h]⟩

theorem c923 : Colours (923 : V) 0 0 0 438 := by
  simpa using colours_of (V := V) t923
theorem c924 : Colours (924 : V) 0 1 0 438 := by
  simpa using colours_of (V := V) t924
theorem c925 : Colours (925 : V) 0 432 0 438 := by
  simpa using colours_of (V := V) t925
theorem c926 : Colours (926 : V) 0 433 0 438 := by
  simpa using colours_of (V := V) t926
theorem c927 : Colours (927 : V) 2 434 2 0 := by
  simpa using colours_of (V := V) t927
theorem c928 : Colours (928 : V) 3 436 4 4 := by
  simpa using colours_of (V := V) t928
theorem c929 : Colours (929 : V) 4 436 4 0 := by
  simpa using colours_of (V := V) t929
theorem c930 : Colours (930 : V) 1 438 1 434 := by
  simpa using colours_of (V := V) t930
theorem c931 : Colours (931 : V) 1 438 1 435 := by
  simpa using colours_of (V := V) t931
theorem c932 : Colours (932 : V) 1 438 1 436 := by
  simpa using colours_of (V := V) t932
theorem c933 : Colours (933 : V) 0 437 0 437 := by
  simpa using colours_of (V := V) t933
theorem c934 : Colours (934 : V) 0 437 1 437 := by
  simpa using colours_of (V := V) t934
theorem c938 : Colours (938 : V) 1 437 2 437 := by
  simpa using colours_of (V := V) t938
theorem c939 : Colours (939 : V) 4 437 0 437 := by
  simpa using colours_of (V := V) t939
theorem c431 : Colours (431 : V) 0 432 0 432 := by
  simpa using colours_of (V := V) t431
theorem c432 : Colours (432 : V) 0 433 0 433 := by
  simpa using colours_of (V := V) t432
theorem c433 : Colours (433 : V) 0 0 0 0 := by
  simpa using colours_of (V := V) t433
theorem c434 : Colours (434 : V) 0 1 0 1 := by
  simpa using colours_of (V := V) t434
theorem c0 : Colours (0 : V) 2 435 3 1 := ⟨westC_zero, northC_zero, eastC_zero, southC_zero⟩

theorem bit_cases' {b : V} (hb : b ≤ 1) : b = 0 ∨ b = 1 := le_one_iff_eq_zero_or_one.mp hb

/-- Plain pass tile `433+b`. -/
theorem pass_colours {b : V} (hb : b ≤ 1) : Colours (433 + b) 0 b 0 b := by
  rcases bit_cases' hb with rfl | rfl
  · simpa using c433 (V := V)
  · convert c434 (V := V) using 1; norm_num

/-- Halted head pass tile `431+b`. -/
theorem halt_colours {b : V} (hb : b ≤ 1) : Colours (431 + b) 0 (432 + b) 0 (432 + b) := by
  rcases bit_cases' hb with rfl | rfl
  · simpa using c431 (V := V)
  · convert c432 (V := V) using 1 <;> norm_num

/-- Finish tiles `923+b` and `925+b`. -/
theorem finish_colours {b : V} (hb : b ≤ 1) : Colours (923 + b) 0 b 0 438 := by
  rcases bit_cases' hb with rfl | rfl
  · simpa using c923 (V := V)
  · convert c924 (V := V) using 1; norm_num

theorem finish_head_colours {b : V} (hb : b ≤ 1) : Colours (925 + b) 0 (432 + b) 0 438 := by
  rcases bit_cases' hb with rfl | rfl
  · simpa using c925 (V := V)
  · convert c926 (V := V) using 1 <;> norm_num

theorem pass_lt {b : V} (hb : b ≤ 1) : (433 : V) + b < 942 :=
  lt_of_le_of_lt (add_le_add le_rfl hb) (by norm_num)
theorem halt_lt {b : V} (hb : b ≤ 1) : (431 : V) + b < 942 :=
  lt_of_le_of_lt (add_le_add le_rfl hb) (by norm_num)
theorem finish_lt {b : V} (hb : b ≤ 1) : (923 : V) + b < 942 :=
  lt_of_le_of_lt (add_le_add le_rfl hb) (by norm_num)
theorem finish_head_lt {b : V} (hb : b ≤ 1) : (925 : V) + b < 942 :=
  lt_of_le_of_lt (add_le_add le_rfl hb) (by norm_num)

/-- The operating head tile of state code `st ∈ [1,215]` reading `b0`, and the
receiver of its rail for every received bit `b`. -/
theorem head_receiver {st b0 : V} (hst0 : st ≠ 0) (hst : st ≤ 215) (hb0 : b0 ≤ 1) :
    2 * st + b0 - 1 < 942 ∧ northC (2 * st + b0 - 1) = 2 * st + b0 ∧
    ∀ b : V, b ≤ 1 →
      423 + 2 * (eastC (2 * st + b0 - 1) + westC (2 * st + b0 - 1)) + b < 942 ∧
      westC (423 + 2 * (eastC (2 * st + b0 - 1) + westC (2 * st + b0 - 1)) + b) =
        eastC (2 * st + b0 - 1) ∧
      northC (423 + 2 * (eastC (2 * st + b0 - 1) + westC (2 * st + b0 - 1)) + b) = b ∧
      eastC (423 + 2 * (eastC (2 * st + b0 - 1) + westC (2 * st + b0 - 1)) + b) =
        westC (2 * st + b0 - 1) := by
  obtain ⟨p, hp, rfl⟩ := standard_of_lt (n := 216) (i := st)
    (lt_of_le_of_lt hst (by norm_num))
  obtain ⟨β, hβ, rfl⟩ := standard_of_lt (n := 2) (i := b0)
    (lt_of_le_of_lt hb0 (by norm_num))
  have hp0 : p ≠ 0 := by rintro rfl; exact hst0 (by simp)
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hi : (2 * ((q + 1 : ℕ) : V) + (β : V) - 1) = (((2 * q + β) + 1 : ℕ) : V) := by
    rw [show (2 * ((q + 1 : ℕ) : V) + (β : V)) = (((2 * q + β) + 1 : ℕ) : V) + 1 by push_cast; ring]
    exact add_tsub_cancel_right _ _
  rw [hi]
  have hj : 2 * q + β < 430 := by omega
  let j : Fin 430 := ⟨2 * q + β, hj⟩
  refine ⟨by exact_mod_cast (show 2 * q + β + 1 < 942 by omega), ?_, ?_⟩
  · obtain ⟨E, W, hT, -, -⟩ := trans_shape j 0 (by norm_num)
    have hT' : tileN (2 * q + β + 1) = ⟨W, 2 * q + β + 2, E, (action j).1.toNat⟩ := hT
    rw [northC_cast, hT']; push_cast; ring
  · intro b hb
    obtain ⟨γ, hγ, rfl⟩ := standard_of_lt (n := 2) (i := b)
      (lt_of_le_of_lt hb (by norm_num))
    obtain ⟨E, W, hT, hlt, hR⟩ := trans_shape j γ hγ
    have hT' : tileN (2 * q + β + 1) = ⟨W, 2 * q + β + 2, E, (action j).1.toNat⟩ := hT
    rw [eastC_cast, westC_cast, hT']
    have hm : (423 : V) + 2 * ((E : ℕ) + (W : ℕ) : V) + (γ : V) =
        ((423 + 2 * (E + W) + γ : ℕ) : V) := by push_cast; ring
    simp only []
    rw [hm, westC_cast, northC_cast, eastC_cast, hR]
    exact ⟨by exact_mod_cast hlt, rfl, rfl, rfl⟩

end DiophantineConsistency.ArithmeticTilingTable
