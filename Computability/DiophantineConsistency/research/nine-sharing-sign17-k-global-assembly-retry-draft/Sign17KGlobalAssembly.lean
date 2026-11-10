import DiophantineConsistency.Sign17KGlobalRankConditional
import DiophantineConsistency.Sign17KGlobalChunk00
import DiophantineConsistency.Sign17KGlobalChunk01
import DiophantineConsistency.Sign17KGlobalChunk02
import DiophantineConsistency.Sign17KGlobalChunk03
import DiophantineConsistency.Sign17KGlobalChunk04
import DiophantineConsistency.Sign17KGlobalChunk05
import DiophantineConsistency.Sign17KGlobalChunk06
import DiophantineConsistency.Sign17KGlobalChunk07
import DiophantineConsistency.Sign17KGlobalChunk08
import DiophantineConsistency.Sign17KGlobalChunk09
import DiophantineConsistency.Sign17KGlobalChunk10
import DiophantineConsistency.Sign17KGlobalChunk11
import DiophantineConsistency.Sign17KGlobalChunk12
import DiophantineConsistency.Sign17KGlobalChunk13
import DiophantineConsistency.Sign17KGlobalChunk14

/-! SOURCE-ONLY: proposed chunk-to-global facts and candidate ranks. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KGlobalAssembly

theorem tail_nonzero : ∀ i : Fin 941, Sign17KWeightUnion942.indices i.succ ≠ 0 := by
  intro i
  refine Fin.addCases (m := 64) (n := 877) ?_ ?_ i
  · intro x0
    simpa only [Sign17KGlobalChunk00.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk00.nonzero x0
  · intro j0
    refine Fin.addCases (m := 64) (n := 813) ?_ ?_ j0
    · intro x1
      simpa only [Sign17KGlobalChunk01.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk01.nonzero x1
    · intro j1
      refine Fin.addCases (m := 64) (n := 749) ?_ ?_ j1
      · intro x2
        simpa only [Sign17KGlobalChunk02.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk02.nonzero x2
      · intro j2
        refine Fin.addCases (m := 64) (n := 685) ?_ ?_ j2
        · intro x3
          simpa only [Sign17KGlobalChunk03.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk03.nonzero x3
        · intro j3
          refine Fin.addCases (m := 64) (n := 621) ?_ ?_ j3
          · intro x4
            simpa only [Sign17KGlobalChunk04.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk04.nonzero x4
          · intro j4
            refine Fin.addCases (m := 64) (n := 557) ?_ ?_ j4
            · intro x5
              simpa only [Sign17KGlobalChunk05.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk05.nonzero x5
            · intro j5
              refine Fin.addCases (m := 64) (n := 493) ?_ ?_ j5
              · intro x6
                simpa only [Sign17KGlobalChunk06.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk06.nonzero x6
              · intro j6
                refine Fin.addCases (m := 64) (n := 429) ?_ ?_ j6
                · intro x7
                  simpa only [Sign17KGlobalChunk07.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk07.nonzero x7
                · intro j7
                  refine Fin.addCases (m := 64) (n := 365) ?_ ?_ j7
                  · intro x8
                    simpa only [Sign17KGlobalChunk08.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk08.nonzero x8
                  · intro j8
                    refine Fin.addCases (m := 64) (n := 301) ?_ ?_ j8
                    · intro x9
                      simpa only [Sign17KGlobalChunk09.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk09.nonzero x9
                    · intro j9
                      refine Fin.addCases (m := 64) (n := 237) ?_ ?_ j9
                      · intro x10
                        simpa only [Sign17KGlobalChunk10.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk10.nonzero x10
                      · intro j10
                        refine Fin.addCases (m := 64) (n := 173) ?_ ?_ j10
                        · intro x11
                          simpa only [Sign17KGlobalChunk11.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk11.nonzero x11
                        · intro j11
                          refine Fin.addCases (m := 64) (n := 109) ?_ ?_ j11
                          · intro x12
                            simpa only [Sign17KGlobalChunk12.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk12.nonzero x12
                          · intro j12
                            refine Fin.addCases (m := 64) (n := 45) ?_ ?_ j12
                            · intro x13
                              simpa only [Sign17KGlobalChunk13.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk13.nonzero x13
                            · intro j13
                              simpa only [Sign17KGlobalChunk14.nonzeroIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk14.nonzero j13

theorem numeric_adjacent : ∀ i : Fin 940, Sign17KWeightUnion942.weights i.succ.succ < Sign17KWeightUnion942.weights i.castSucc.succ := by
  intro i
  refine Fin.addCases (m := 64) (n := 876) ?_ ?_ i
  · intro x0
    simpa only [Sign17KGlobalChunk00.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk00.adjacent x0
  · intro j0
    refine Fin.addCases (m := 64) (n := 812) ?_ ?_ j0
    · intro x1
      simpa only [Sign17KGlobalChunk01.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk01.adjacent x1
    · intro j1
      refine Fin.addCases (m := 64) (n := 748) ?_ ?_ j1
      · intro x2
        simpa only [Sign17KGlobalChunk02.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk02.adjacent x2
      · intro j2
        refine Fin.addCases (m := 64) (n := 684) ?_ ?_ j2
        · intro x3
          simpa only [Sign17KGlobalChunk03.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk03.adjacent x3
        · intro j3
          refine Fin.addCases (m := 64) (n := 620) ?_ ?_ j3
          · intro x4
            simpa only [Sign17KGlobalChunk04.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk04.adjacent x4
          · intro j4
            refine Fin.addCases (m := 64) (n := 556) ?_ ?_ j4
            · intro x5
              simpa only [Sign17KGlobalChunk05.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk05.adjacent x5
            · intro j5
              refine Fin.addCases (m := 64) (n := 492) ?_ ?_ j5
              · intro x6
                simpa only [Sign17KGlobalChunk06.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk06.adjacent x6
              · intro j6
                refine Fin.addCases (m := 64) (n := 428) ?_ ?_ j6
                · intro x7
                  simpa only [Sign17KGlobalChunk07.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk07.adjacent x7
                · intro j7
                  refine Fin.addCases (m := 64) (n := 364) ?_ ?_ j7
                  · intro x8
                    simpa only [Sign17KGlobalChunk08.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk08.adjacent x8
                  · intro j8
                    refine Fin.addCases (m := 64) (n := 300) ?_ ?_ j8
                    · intro x9
                      simpa only [Sign17KGlobalChunk09.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk09.adjacent x9
                    · intro j9
                      refine Fin.addCases (m := 64) (n := 236) ?_ ?_ j9
                      · intro x10
                        simpa only [Sign17KGlobalChunk10.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk10.adjacent x10
                      · intro j10
                        refine Fin.addCases (m := 64) (n := 172) ?_ ?_ j10
                        · intro x11
                          simpa only [Sign17KGlobalChunk11.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk11.adjacent x11
                        · intro j11
                          refine Fin.addCases (m := 64) (n := 108) ?_ ?_ j11
                          · intro x12
                            simpa only [Sign17KGlobalChunk12.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk12.adjacent x12
                          · intro j12
                            refine Fin.addCases (m := 64) (n := 44) ?_ ?_ j12
                            · intro x13
                              simpa only [Sign17KGlobalChunk13.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk13.adjacent x13
                            · intro j13
                              simpa only [Sign17KGlobalChunk14.adjacentIndex, Fin.natAdd, Fin.castAdd, Fin.castLE_mk, Fin.val_castLE, ← Nat.add_assoc, Nat.reduceAdd, Nat.zero_add, Nat.add_zero] using Sign17KGlobalChunk14.adjacent j13

theorem global_nonzero : ∀ i, i ≠ 0 → Sign17KWeightUnion942.indices i ≠ 0 := by
  intro i hi
  cases i using Fin.cases with
  | zero => exact False.elim (hi rfl)
  | succ i => exact tail_nonzero i

theorem candidate_positions : ∀ i, MF.WangTiles942.physicalMap (Sign17KWeightUnion942.indices i) = i := by
  exact Sign17KGlobalRankConditional.candidate_positions_if
    Sign17KGlobalChunk00.start_index global_nonzero numeric_adjacent

end DiophantineConsistency.Sign17KGlobalAssembly
#print axioms DiophantineConsistency.Sign17KGlobalAssembly.tail_nonzero
#print axioms DiophantineConsistency.Sign17KGlobalAssembly.numeric_adjacent
#print axioms DiophantineConsistency.Sign17KGlobalAssembly.global_nonzero
#print axioms DiophantineConsistency.Sign17KGlobalAssembly.candidate_positions
