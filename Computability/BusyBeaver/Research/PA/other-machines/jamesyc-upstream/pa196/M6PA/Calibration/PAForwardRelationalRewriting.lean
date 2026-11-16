module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationRewriting
public import M6PA.Calibration.RelationalOrderIso
@[expose] public section

/-! Target rewriting only; these laws do not substitute source arithmetic terms. -/
namespace M6.PA.RelationalSource
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
set_option maxRecDepth 8192
set_option maxHeartbeats 600000

namespace Ordinal
macro "forwardOrdinalSyntax" : tactic => `(tactic|
  (simp only [successor,zero,subset,transitive,memberTransitive,memberLinear,nonempty,
    least,greatest,internalExtrema,representative,memberIr,domain,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ];
   simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]; finishSourceSyntax))
theorem domain_rew {n m : Nat} (τ : Rew language Nat n Nat m) (z : Term n) :
    Semiformula.rewAux τ (domain z) = domain (τ z) := by forwardOrdinalSyntax
theorem zero_rew {n m : Nat} (τ : Rew language Nat n Nat m) (z : Term n) :
    Semiformula.rewAux τ (zero z) = zero (τ z) := by forwardOrdinalSyntax
theorem successor_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x z : Term n) :
    Semiformula.rewAux τ (successor x z) = successor (τ x) (τ z) := by forwardOrdinalSyntax
end Ordinal
namespace PairGraph
attribute [local irreducible] addResult mulPrefix

theorem mulResult_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x y z : Term n) :
    Semiformula.rewAux τ (mulResult x y z) = mulResult (τ x) (τ y) (τ z) := by
  simp only [mulResult,Semiformula.rewAux,mulPrefix_rew,Ordinal.zero_rew,
    edge,kuratowski,singleton,pair,mem,eq,sourceIff,sourceImply,
    Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  finishSourceSyntax

theorem orderIso_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x y : Term n) :
    Semiformula.rewAux τ (orderIso x y) = orderIso (τ x) (τ y) := by
  simp only [orderIso,orderBijection,graphEntries,entryWitness,graphTyped,
    graphLeftTotal,graphRightTotal,graphFunctional,graphInjective,graphOrder,
    edge,kuratowski,singleton,pair,mem,eq,sourceIff,sourceImply,
    Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  simp only [Function.comp_def,Matrix.comp_vecCons,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ]
  finishSourceSyntax
#print axioms mulResult_rew
#print axioms orderIso_rew
#print axioms Ordinal.domain_rew
end PairGraph
end M6.PA.RelationalSource

