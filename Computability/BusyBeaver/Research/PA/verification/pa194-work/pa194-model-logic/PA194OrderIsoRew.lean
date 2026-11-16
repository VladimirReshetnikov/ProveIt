import PA194ForwardTermCorrect
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
theorem orderIso_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x y : Term n) :
    Semiformula.rewAux τ (orderIso x y) = orderIso (τ x) (τ y) := by
  simp only [orderIso,orderBijection,graphEntries,entryWitness,graphTyped,
    graphLeftTotal,graphRightTotal,graphFunctional,graphInjective,graphOrder,
    edge,kuratowski,singleton,pair,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  finishSourceSyntax
#print axioms orderIso_rew
end M6.PA.RelationalSource.PairGraph
