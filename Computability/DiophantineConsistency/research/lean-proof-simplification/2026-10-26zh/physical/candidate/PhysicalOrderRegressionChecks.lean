import DiophantineConsistency.WangTiles942PhysicalOrderChecks

/-! Candidate-only regression: elaborate with the chosen replacement module,
not the original upstream object. This file has NOT been compiled in this review. -/
namespace DiophantineConsistency.WangTiles942PhysicalOrderRegressionChecks
open WangTiles942PhysicalOrder

/-- The library predecessor preserves the original computational definition. -/
example (j : Fin 941) : nonStartIndex j =
    ⟨(abstractIndex j).val-1, by
      have := (abstractIndex j).isLt
      have := abstractIndex_ne_zero j
      have hp : 0 < (abstractIndex j).val := Fin.pos_iff_ne_zero.mpr this
      omega⟩ := rfl

example {n : ℕ} (f : Fin n → Fin n) (hf : StrictMono f) (i : Fin n) : f i = i :=
  strictMono_fin_eq_self f hf i

#print axioms strictMono_fin_eq_self
#print axioms nonStartIndex_succ
end DiophantineConsistency.WangTiles942PhysicalOrderRegressionChecks
