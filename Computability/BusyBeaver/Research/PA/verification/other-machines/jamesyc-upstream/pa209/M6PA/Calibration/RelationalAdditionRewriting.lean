module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionTrace
@[expose] public section

/-! Capture-aware rewriting for the fixed addition-result formula. This keeps
nested additive traces opaque in later multiplicative witness constructions. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

set_option maxRecDepth 8192
set_option maxHeartbeats 600000

theorem addResult_rew {n m : Nat} (ω : Rew language Nat n Nat m)
    (x y z : Term n) :
    Semiformula.rewAux ω (addResult x y z) = addResult (ω x) (ω y) (ω z) := by
  simp only [addResult,addPrefix,addRecurrence,graphDomain,graphFunctional,graphRange,
    edge,kuratowski,singleton,pair,Ordinal.successor,Ordinal.zero,Ordinal.subset,
    Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,Ordinal.nonempty,
    Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  finishSourceSyntax

#print axioms addResult_rew
end M6.PA.RelationalSource.PairGraph

