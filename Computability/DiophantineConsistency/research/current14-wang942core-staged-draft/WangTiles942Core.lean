import DiophantineConsistency.WangTiles942CoreB

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

theorem all_rows_tight : ∀ row ∈ orderedRows, TightColorsBounded row.2 := by
  simp only [orderedRows, List.forall_mem_append]
  exact ⟨⟨⟨⟨by decide +kernel, List.forall_mem_ofFn_iff.mpr transition_bounded⟩,
    ⟨copies_bounded 1, copies_bounded 0⟩⟩,
    ⟨signals_bounded true, signals_bounded false⟩⟩, tail_bounded⟩

theorem all_rows_bounded : ∀ row ∈ orderedRows, ColorsBounded row.2 := by
  intro row hr
  obtain ⟨hw,he,hn,hs⟩ := all_rows_tight row hr
  exact ⟨hw,he,by omega,by omega⟩

theorem tile_bounded (i : Fin 942) : ColorsBounded (tile i) := by
  exact all_rows_bounded _ (List.getElem_mem _)

theorem start_zero : tile 0 = ⟨2,435,3,1⟩ := by decide +kernel

theorem initializer_928 : tile 928 = ⟨3,436,4,4⟩ := by decide +kernel

theorem actual_first_action : action 0 = (true,true,1) := by decide +kernel

theorem first_transition : tile 1 = ⟨0,2,7,1⟩ := by decide +kernel

theorem empty_interval : rail false 0 = 205 ∧ rail true 0 = 6 := by decide +kernel

theorem all_weights_small : ∀ row ∈ orderedRows, selectorWeight row.2 < 2 ^ 44 := by
  intro row hr
  obtain ⟨hw,he,hn,hs⟩ := all_rows_tight row hr
  dsimp only [selectorWeight]
  omega

theorem weight_small (i : Fin 942) : selectorWeight (tile i) < 2 ^ 44 :=
  all_weights_small _ (List.getElem_mem _)

/-- Thus the subtraction in the natural-number floor numerator never truncates. -/
theorem rank_numerator_nonnegative (i j : Fin 942) :
    selectorWeight (tile i) ≤ 2 ^ 44 - 1 + selectorWeight (tile j) := by
  have hi := weight_small i
  omega

theorem nonStart_rows : (orderedRows.drop 1).map Prod.snd =
    List.ofFn (fun j : Fin 941 => tile ⟨j.val + 1, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_drop, List.length_ofFn, ordered_count]
  · intro j h₁ h₂
    simp only [List.getElem_map, List.getElem_drop, List.getElem_ofFn, tile,
      Nat.add_comm]

/-- Exact equality with the printed floor-rank formula on the abstract domain. -/
theorem physicalPosition_eq_printed (i : Fin 942) : physicalPosition i =
    if i.val = 0 then 0 else 1 + ∑ j : Fin 941,
      (2 ^ 44 - 1 + selectorWeight (tile ⟨j.val + 1, by omega⟩) -
        selectorWeight (tile i)) / 2 ^ 44 := by
  unfold physicalPosition
  have hs := congrArg (fun ts : List Tile =>
    (ts.map (fun t => (2 ^ 44 - 1 + selectorWeight t - selectorWeight (tile i)) /
      2 ^ 44)).sum) nonStart_rows
  simpa only [List.map_map, List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    congrArg (fun x : ℕ => if i.val = 0 then 0 else 1 + x) hs

end DiophantineConsistency.WangTiles942
