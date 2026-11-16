import PA194MulZeroPoint
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194ForwardMulZero
open LO LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

theorem edge_rew {n m : Nat} (τ : Rew language Nat n Nat m) (g x y : Ordinal.Term n) :
    Semiformula.rewAux τ (edge g x y) = edge (τ g) (τ x) (τ y) := by
  simp only [edge,kuratowski,PairGraph.singleton,PairGraph.pair,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  finishSourceSyntax
#print axioms edge_rew
end PA194ForwardMulZero
