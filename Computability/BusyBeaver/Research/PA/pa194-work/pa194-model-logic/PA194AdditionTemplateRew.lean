import PA194FoundationAdditionTrace
import PA194OrdinalTemplateRew
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
@[simp] theorem q_q_q_q_bvar_three {n m : Nat} (τ : Rew language Nat n Nat m) :
    τ.q.q.q.q (.bvar (3 : Fin (n+4))) = .bvar 3 := by
  change τ.q.q.q.q (.bvar (Fin.succ (Fin.succ (Fin.succ (0 : Fin (n+1)))))) = _
  rw [Rew.q_bvar_succ,Rew.q_bvar_succ,Rew.q_bvar_succ,Rew.q_bvar_zero]
  rfl

theorem addResult_rew {n m : Nat} (ω : Rew language Nat n Nat m)
    (x y z : Term n) :
    Semiformula.rewAux ω (addResult x y z) = addResult (ω x) (ω y) (ω z) := by
  simp only [addResult,addPrefix,addRecurrence,graphDomain,graphFunctional,graphRange,
    edge,kuratowski,singleton,pair,Ordinal.successor,Ordinal.zero,Ordinal.subset,
    Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,Ordinal.nonempty,
    Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  simp only [Function.comp_def,Matrix.comp_vecCons, Rew.q_comp_bShift_app, Rew.q_bvar_zero, Rew.q_bvar_succ, Ordinal.q_q_bvar_one, Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  finishSourceSyntax
#print axioms addResult_rew
end M6.PA.RelationalSource.PairGraph
