import PA194AdditionCoherenceApply
import PA194ModelStandardNoFree
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
namespace PA194AdditionCoherenceClosed
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.PairGraph

theorem noFree : addCoherenceStatement.freeVariables = ∅ := by decide

theorem shift : addCoherenceStatement.shift = addCoherenceStatement :=
  PA194ModelLogic.syntactic_noFree_shift_fixed 0 addCoherenceStatement noFree

#print axioms noFree
#print axioms shift
end PA194AdditionCoherenceClosed
