import DiophantineConsistency.WangTiles942CoreA

namespace DiophantineConsistency.WangTiles942
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

theorem target_counts_true : (targets true).card = 199 := by
  decide +kernel

end DiophantineConsistency.WangTiles942
#print axioms DiophantineConsistency.WangTiles942.target_counts_true
