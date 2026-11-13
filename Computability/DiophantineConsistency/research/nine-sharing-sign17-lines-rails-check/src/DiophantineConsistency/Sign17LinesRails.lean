import DiophantineConsistency.Sign17LinesDecoder

/-! SOURCE ONLY. Target sets and rail values from the 715 in-Lean digits. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17LinesRails

open Sign17LinesDecoder

def lineActions : List WangTiles942.Action :=
  List.ofFn (fun j : Fin 430 => Sign17ParamDecoder.actionAt displayedSeed j.val)

theorem cached_actions_from_lines : WangTiles942.cachedActions = lineActions := by
  unfold WangTiles942.cachedActions lineActions
  apply congrArg List.ofFn
  funext j
  exact cache_from_lines j

theorem target_set_from_lines (d : Bool) : WangTiles942.targets d =
    WangTiles942.targetsFrom d lineActions := by
  rw [WangTiles942.targets_eq_cache, cached_actions_from_lines]

theorem rail_from_lines (d : Bool) (q : ℕ) : WangTiles942.rail d q =
    205 - 199 * d.toNat +
      (WangTiles942.targetsFrom d lineActions ∩ Finset.range q).card := by
  rw [WangTiles942.rail_eq_formula, WangTiles942.railFormula, target_set_from_lines]

theorem transition_row_from_lines_and_rails (j : Fin 430) :
    WangTiles942.transitionRow j =
      let a := Sign17ParamDecoder.actionAt displayedSeed j.val
      let d := a.2.1.toNat
      (j.val + 1, ⟨(1-d) * (205 - 199 * false.toNat +
          (WangTiles942.targetsFrom false lineActions ∩ Finset.range a.2.2).card),
        WangTiles942.headColor (j.val / 2) (j.val % 2),
        d * (205 - 199 * true.toNat +
          (WangTiles942.targetsFrom true lineActions ∩ Finset.range a.2.2).card),
        a.1.toNat⟩) := by
  simp only [transition_row_from_lines, rail_from_lines]

end DiophantineConsistency.Sign17LinesRails
#print axioms DiophantineConsistency.Sign17LinesRails.cached_actions_from_lines
#print axioms DiophantineConsistency.Sign17LinesRails.target_set_from_lines
#print axioms DiophantineConsistency.Sign17LinesRails.rail_from_lines
#print axioms DiophantineConsistency.Sign17LinesRails.transition_row_from_lines_and_rails
