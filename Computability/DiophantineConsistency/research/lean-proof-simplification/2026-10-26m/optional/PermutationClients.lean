import DiophantineConsistency.WangTiles942Permutation

namespace DiophantineConsistency.WangTiles942

theorem nonStartWeight_injective_short : Function.Injective nonStartWeight :=
  tile_weight_injective.comp (Fin.succ_injective 941)

theorem physicalPosition_injective_short : Function.Injective physicalPosition := by
  have hform : physicalPosition =
      Fin.cons 0 (fun i : Fin 941 => 1 + strictRank nonStartWeight i) :=
    funext (Fin.cases physicalPosition_zero physicalPosition_succ)
  rw [hform]
  exact Fin.cons_injective_iff.mpr ⟨by simp,
    fun i j h => strictRank_injective nonStartWeight_injective (Nat.add_left_cancel h)⟩

#print axioms nonStartWeight_injective_short
#print axioms physicalPosition_injective_short

end DiophantineConsistency.WangTiles942
