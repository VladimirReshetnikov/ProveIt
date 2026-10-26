import DiophantineConsistency.WangTiles942Core

/-!
# The initializer's exact position in the printed floor ranking

The imported core binds every table row to the actual decimal decoder.
This module proves the complete initializer rank by table-family sums.
-/

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

def initializerScore (t : Tile) : ℕ :=
  (2 ^ 44 - 1 + selectorWeight t - selectorWeight ⟨3,436,4,4⟩) / 2 ^ 44

theorem initializerScore_zero (t : Tile) (ht : TightColorsBounded t)
    (hs : t.south ≤ 3) : initializerScore t = 0 := by
  obtain ⟨hw,he,hn,_⟩ := ht
  dsimp only [initializerScore, selectorWeight]
  omega

theorem transition_initializerScore (j : Fin 430) :
    initializerScore (transitionRow j).2 = 0 := by
  apply initializerScore_zero _ (transition_bounded j)
  have h := Bool.toNat_le (action j).1
  change (action j).1.toNat ≤ 3
  omega

theorem transition_initializerScore_sum :
    ((List.ofFn transitionRow).map (fun row => initializerScore row.2)).sum = 0 := by
  apply List.sum_eq_zero_iff_forall_eq_nat.mpr
  intro x hx
  obtain ⟨row,hr,rfl⟩ := List.mem_map.mp hx
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
  exact transition_initializerScore j

theorem initializerScore_one (t : Tile) (ht : TightColorsBounded t)
    (hs : 5 ≤ t.south) : initializerScore t = 1 := by
  obtain ⟨hw,he,hn,hs'⟩ := ht
  dsimp only [initializerScore, selectorWeight]
  omega

theorem left_targets_ge_four : ∀ q ∈ targetList false, 4 ≤ q := by
  decide +kernel

def signalScore (d : Bool) (q b : ℕ) : ℕ :=
  if d then (if q = 0 then 0 else if q = 1 then b else 1) else 1

theorem rail_true_one : rail true 1 = 7 := by decide +kernel

theorem signal_initializerScore (d : Bool) (q b : ℕ)
    (hq : q ∈ targetList d) (hb : b ∈ List.range 2) :
    initializerScore ⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩ =
      signalScore d q b := by
  have ht := signals_bounded d _ (List.mem_flatMap.mpr
    ⟨q,hq,List.mem_map.mpr ⟨b,hb,rfl⟩⟩)
  have hb' : b < 2 := List.mem_range.mp hb
  cases d
  · have hq' := left_targets_ge_four q hq
    exact initializerScore_one _ ht (by dsimp [headColor]; omega)
  · by_cases hq0 : q = 0
    · calc
        _ = 0 := initializerScore_zero _ ht (by dsimp [headColor]; omega)
        _ = signalScore true q b := by simp only [signalScore, hq0, ↓reduceIte]
    · by_cases hq1 : q = 1
      · by_cases hb0 : b = 0
        · have hs : initializerScore ⟨7,0,0,4⟩ = 0 := by decide +kernel
          calc
            _ = 0 := by
              simpa only [hq1, hb0, Bool.toNat_true, Nat.one_mul,
                Nat.sub_self, Nat.zero_mul, headColor, rail_true_one] using hs
            _ = signalScore true q b := by
              simp only [signalScore, hq1, hb0, Nat.one_ne_zero, ↓reduceIte]
        · have hb1 : b = 1 := by omega
          calc
            _ = 1 := initializerScore_one _ ht (by dsimp [headColor]; omega)
            _ = signalScore true q b := by
              simp only [signalScore, hq1, hb1, Nat.one_ne_zero, ↓reduceIte]
      · calc
          _ = 1 := initializerScore_one _ ht (by dsimp [headColor]; omega)
          _ = signalScore true q b := by
            simp only [signalScore, hq0, hq1, ↓reduceIte]

private theorem map_nested_of_pointwise {α β γ δ : Type*}
    (xs : List α) (ys : α → List β) (f : α → β → γ)
    (g : γ → δ) (h : α → β → δ)
    (he : ∀ a ∈ xs, ∀ b ∈ ys a, g (f a b) = h a b) :
    (xs.flatMap (fun a => (ys a).map (f a))).map g =
      xs.flatMap (fun a => (ys a).map (h a)) := by
  rewrite [List.map_flatMap]
  apply List.flatMap_congr
  intro a ha
  rewrite [List.map_map]
  apply List.map_congr_left
  intro b hb
  exact he a ha b hb

theorem signal_initializerScore_map (d : Bool) :
    (signalRows d).map (fun row => initializerScore row.2) =
      (targetList d).flatMap (fun q => (List.range 2).map (signalScore d q)) :=
  map_nested_of_pointwise (targetList d) (fun _ => List.range 2)
    (fun q b => (423+2*rail d q+b,
      (⟨d.toNat*rail d q,b,(1-d.toNat)*rail d q,headColor q b⟩ : Tile)))
    (fun row => initializerScore row.2) (signalScore d)
    (fun q hq b hb => signal_initializerScore d q b hq hb)

theorem signal_initializerScore_sums :
    ((signalRows true).map (fun row => initializerScore row.2)).sum = 395 ∧
    ((signalRows false).map (fun row => initializerScore row.2)).sum = 90 := by
  rewrite [signal_initializerScore_map, signal_initializerScore_map]
  decide +kernel

private theorem drop_start {α : Type*} (a : α) (l₁ l₂ l₃ l₄ : List α) :
    ((([a] ++ l₁) ++ l₂) ++ l₃ ++ l₄).drop 1 = l₁ ++ l₂ ++ l₃ ++ l₄ := by
  simp only [List.append_assoc, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

private theorem sum_map_four {α : Type*} (f : α → ℕ) (l₁ l₂ l₃ l₄ : List α) :
    ((l₁ ++ l₂ ++ l₃ ++ l₄).map f).sum =
      (l₁.map f).sum + (l₂.map f).sum + (l₃.map f).sum + (l₄.map f).sum := by
  simp only [List.map_append, List.sum_append]

theorem position_of_tile (i : Fin 942) (hi : i.val ≠ 0) (t : Tile) (ht : tile i = t) :
    physicalPosition i = 1 + ((orderedRows.drop 1).map (fun row =>
      (2 ^ 44 - 1 + selectorWeight row.2 - selectorWeight t) / 2 ^ 44)).sum := by
  unfold physicalPosition
  rw [if_neg hi, ht]

private theorem sum_map_append_eq {α : Type*} (f : α → ℕ) (l₁ l₂ : List α)
    (n₁ n₂ : ℕ) (h₁ : (l₁.map f).sum = n₁) (h₂ : (l₂.map f).sum = n₂) :
    ((l₁ ++ l₂).map f).sum = n₁ + n₂ := by
  rw [List.map_append, List.sum_append, h₁, h₂]

private theorem sum_drop_start_eq {α : Type*} (a : α) (f : α → ℕ)
    (l₁ l₂ l₃ l₄ : List α) (n₁ n₂ n₃ n₄ : ℕ)
    (h₁ : (l₁.map f).sum = n₁) (h₂ : (l₂.map f).sum = n₂)
    (h₃ : (l₃.map f).sum = n₃) (h₄ : (l₄.map f).sum = n₄) :
    (((([a] ++ l₁) ++ l₂) ++ l₃ ++ l₄).drop 1 |>.map f).sum =
      n₁ + n₂ + n₃ + n₄ := by
  rw [drop_start, sum_map_four, h₁, h₂, h₃, h₄]

theorem copy_initializerScore_sum :
    ((copyRows 1 ++ copyRows 0).map (fun row => initializerScore row.2)).sum = 2 := by
  decide +kernel

theorem tail_initializerScore_sum :
    (tailRows.map (fun row => initializerScore row.2)).sum = 16 := by
  decide +kernel

theorem both_signal_initializerScore_sum :
    ((signalRows true ++ signalRows false).map (fun row => initializerScore row.2)).sum = 485 :=
  sum_map_append_eq _ _ _ 395 90 signal_initializerScore_sums.1 signal_initializerScore_sums.2

theorem nonStart_initializerScore_sum :
    ((orderedRows.drop 1).map (fun row => initializerScore row.2)).sum = 503 :=
  sum_drop_start_eq (0,start) (fun row => initializerScore row.2)
    (List.ofFn transitionRow) (copyRows 1 ++ copyRows 0)
    (signalRows true ++ signalRows false) tailRows 0 2 485 16
    transition_initializerScore_sum copy_initializerScore_sum
    both_signal_initializerScore_sum tail_initializerScore_sum

theorem initializer_position : physicalPosition 928 = 504 := by
  have hf : (fun row : ℕ × Tile =>
      (2 ^ 44 - 1 + selectorWeight row.2 - selectorWeight (⟨3,436,4,4⟩ : Tile)) / 2 ^ 44) =
      (fun row => initializerScore row.2) := rfl
  have he := congrArg (fun f : (ℕ × Tile) → ℕ =>
    1 + ((orderedRows.drop 1).map f).sum) hf
  exact (position_of_tile 928 (by decide) ⟨3,436,4,4⟩ initializer_928).trans
    (he.trans (congrArg (fun n : ℕ => 1+n) nonStart_initializerScore_sum))

/-- The initializer's head color uses the actual decoded first target, not
the former dense state name or a presumed numeric target. -/
theorem initializer_actual_target :
    (tile 928).south = headColor (DecimalMachine215.action 0).2.2 0 := by
  have h : DecimalMachine215.action 0 = (true,true,1) :=
    (action_eq_decoder (0 : Fin 430)).symm.trans actual_first_action
  rw [initializer_928, h]
  rfl

theorem physical_initializer : physicalPosition 928 = 504 ∧
    tile 928 = ⟨3,436,4,4⟩ ∧
    (tile 928).south = headColor (DecimalMachine215.action 0).2.2 0 :=
  ⟨initializer_position, initializer_928, initializer_actual_target⟩

end DiophantineConsistency.WangTiles942
