module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationTrace
public import M6PA.Calibration.RelationalAdditionRewriting
@[expose] public section

/-! Compositional multiplication rewriting: additive traces remain opaque. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000
attribute [local irreducible] addResult

theorem mulPrefix_rew {n m : Nat} (ω : Rew language Nat n Nat m)
    (top base zero g : Term n) :
    Semiformula.rewAux ω (mulPrefix top base zero g) =
      mulPrefix (ω top) (ω base) (ω zero) (ω g) := by
  simp only [mulPrefix,mulRecurrence,addResult_rew,graphDomain,graphFunctional,graphRange,
    edge,kuratowski,singleton,pair,Ordinal.successor,Ordinal.zero,Ordinal.subset,
    Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,Ordinal.nonempty,
    Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  finishSourceSyntax

#print axioms mulPrefix_rew
end M6.PA.RelationalSource.PairGraph

