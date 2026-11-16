import PA194MulZeroEq
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

theorem equalAt_shift (b : Nat) : (equalAt b).shift = equalAt (b+1) := by
  change Semiformula.rewAux Rew.shift (equalAt b) = _
  simp [equalAt,Semiformula.rewAux,domain_rew,zero_rew,mulResult_rew,orderIso_rew,eq,Rew.shift,Rew.map,Rew.q]
#print axioms equalAt_shift
end PA194ForwardMulZero
