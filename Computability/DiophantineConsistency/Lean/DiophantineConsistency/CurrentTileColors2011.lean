import DiophantineConsistency.CurrentWholeField2011
import DiophantineConsistency.CurrentAdjacency2011

/-!
# True tile-color matching on the original arithmetic word

The selected indices remain explicit in the local color lemmas. All label,
phase, copy and mask premises are derived from the same original Facts.
Even before proving all-cell occupation, Start rules out a zero temporal
displacement in the full cyclic word.
-/

namespace DiophantineConsistency.CurrentTileColors2011

open CurrentPolynomialWindow2011 CurrentCellLabels2011 CurrentDecodedWindow2011
  CurrentWholeField2011 CurrentAdjacency2011 WangTiles942

set_option Elab.async false

theorem binaryWord_congr (f g : ℕ → ℕ) (n : ℕ)
    (h : ∀ j, j < n → f j = g j) : binaryWord f n = binaryWord g n := by
  unfold binaryWord
  apply Finset.sum_congr rfl
  intro j hj
  rw [h j (Finset.mem_range.mp hj)]

variable {N : ℕ} [NeZero (N * 2011)]

/-- The four labels of a supplied selected index come from the actual
clause, with every native premise discharged by the original Facts. -/
theorem facts_selected_labels (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (i : Fin 942)
    (hi : selectorValue c b i = 1) :
    binaryWord (fun j => c (b + ((978+j : ℕ) : ZMod (N*2011)))) 8 = 255-(tile i).west ∧
    binaryWord (fun j => c (b + ((960+j : ℕ) : ZMod (N*2011)))) 9 = 511-(tile i).north ∧
    binaryWord (fun j => c (b + ((969+j : ℕ) : ZMod (N*2011)))) 8 = 255-(tile i).east ∧
    binaryWord (fun j => c (b + ((942+j : ℕ) : ZMod (N*2011)))) 9 = 511-(tile i).south := by
  exact labels_of_word c b h.boolean i
    ((facts_decode_cell v x c carry digits h b hb).1.word_of_selected i hi)

/-- The original color orientation is East(current)=West(previous). -/
theorem facts_horizontal_colors (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (i j : Fin 942)
    (hi : selectorValue c b i = 1) (hj : selectorValue c (previousCell b) j = 1) :
    (tile i).east = (tile j).west := by
  have hadj := facts_adjacency v x c carry digits h
    (facts_whole_field v x c carry digits h) b hb
  have hl := facts_selected_labels v x c carry digits h b hb i hi
  have hr := facts_selected_labels v x c carry digits h (previousCell b) hadj.1 j hj
  have hw := binaryWord_congr
    (fun k => c (b + ((969+k : ℕ) : ZMod (N*2011))))
    (fun k => c (previousCell b + ((978+k : ℕ) : ZMod (N*2011)))) 8
    (fun k hk => hadj.2.2.1 ⟨k,hk⟩)
  obtain ⟨hiw,hie,hin,his⟩ := tile_bounded i
  obtain ⟨hjw,hje,hjn,hjs⟩ := tile_bounded j
  rw [hl.2.2.1, hr.1] at hw
  omega

/-- The original temporal orientation is South(current)=North(shifted). -/
theorem facts_temporal_colors (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits)
    (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) (i j : Fin 942)
    (hi : selectorValue c b i = 1)
    (hj : selectorValue c
      (temporalCell ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
        47*(N*2011)) b) j = 1) :
    (tile i).south = (tile j).north := by
  have hadj := facts_adjacency v x c carry digits h
    (facts_whole_field v x c carry digits h) b hb
  have hl := facts_selected_labels v x c carry digits h b hb i hi
  have hr := facts_selected_labels v x c carry digits h _ hadj.2.1 j hj
  have hw := binaryWord_congr
    (fun k => c (b + ((942+k : ℕ) : ZMod (N*2011))))
    (fun k => c (temporalCell
      ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47*(N*2011)) b +
        ((960+k : ℕ) : ZMod (N*2011)))) 9
    (fun k hk => hadj.2.2.2 ⟨k,hk⟩)
  obtain ⟨hiw,hie,hin,his⟩ := tile_bounded i
  obtain ⟨hjw,hje,hjn,hjs⟩ := tile_bounded j
  rw [hl.2.2.2, hr.2.1] at hw
  omega

/-- A zero temporal displacement would match Start's South1 to its
North435. This excludes zero modulo the full word, not merely zero as a
natural shift, without assuming occupation anywhere else. -/
theorem facts_temporal_shift_nonzero (v : Fin 14 → ℤ) (x : Fin 31 → ℕ)
    (c carry digits : ZMod (N * 2011) → ℕ) (h : Facts v N x c carry digits) :
    ((((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat -
      47*(N*2011))/47 : ℕ) : ZMod (N*2011)) ≠ 0 := by
  intro hz
  have ht : temporalCell
      ((Carrier65.core CurrentWindowCarry2011.ports v).rank.toNat - 47*(N*2011))
        (0 : ZMod (N*2011)) = 0 := by
    simp only [temporalCell, hz, sub_zero]
  have hs : selectorValue c 0 (0 : Fin 942) = 1 := by
    simpa only [selectorValue, physicalPosition_zero, Nat.cast_zero, zero_add] using h.origin
  have he := facts_temporal_colors v x c carry digits h 0 (by simp) 0 0 hs
    (by simpa only [ht] using hs)
  rw [start_zero] at he
  norm_num at he

end DiophantineConsistency.CurrentTileColors2011
