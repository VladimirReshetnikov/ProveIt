import DiophantineConsistency.Sign17SeedLines
import DiophantineConsistency.Sign17ParamDecoder

/-! SOURCE ONLY. The 715 decimal digits drive the checked transition rows. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17LinesDecoder

def displayedSeed : ℕ := Current14SeedLines.decimalValue Current14SeedLines.digits

theorem cache_from_lines (j : Fin 430) :
    WangTiles942.action j = Sign17ParamDecoder.actionAt displayedSeed j.val := by
  have hs : displayedSeed = DecimalMachine215.seed :=
    Current14SeedLines.decimal_lines_eq_seed.2.2
  rw [hs, Sign17ParamDecoder.action_seed]
  exact WangTiles942.action_eq_decoder j

theorem transition_row_from_lines (j : Fin 430) :
    WangTiles942.transitionRow j =
      let a := Sign17ParamDecoder.actionAt displayedSeed j.val
      let d := a.2.1.toNat
      (j.val + 1, ⟨(1-d) * WangTiles942.rail false a.2.2,
        WangTiles942.headColor (j.val / 2) (j.val % 2),
        d * WangTiles942.rail true a.2.2, a.1.toNat⟩) := by
  simp only [WangTiles942.transitionRow, cache_from_lines]

end DiophantineConsistency.Sign17LinesDecoder
#print axioms DiophantineConsistency.Sign17LinesDecoder.cache_from_lines
#print axioms DiophantineConsistency.Sign17LinesDecoder.transition_row_from_lines
