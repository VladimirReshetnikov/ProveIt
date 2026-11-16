import PA194AdditionTemplateRew
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)
def mulRecurrence {n : Nat} (g base : Term n) : Formula n :=
  ∀⁰ ∀⁰ ∀⁰ sourceImply
    (edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 1) ⋏
      Ordinal.successor (.bvar 0) (.bvar 2))
    (∃⁰ (edge (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift g)))) (.bvar 1) (.bvar 0) ⋏
      addResult (.bvar 0) (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift base)))) (.bvar 2)))
def mulPrefix {n : Nat} (top base zero g : Term n) : Formula n :=
  graphDomain top g ⋏ (graphFunctional g ⋏ (graphRange g ⋏ (edge g zero zero ⋏ mulRecurrence g base)))
def mulResult {n : Nat} (x y z : Term n) : Formula n :=
  ∃⁰ ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift y)) (.bvar 1) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift z))))
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
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  simp only [Function.comp_def,Matrix.comp_vecCons, Rew.q_comp_bShift_app, Rew.q_bvar_zero, Rew.q_bvar_succ, Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  finishSourceSyntax
attribute [local irreducible] mulPrefix
theorem mulResult_rew {n m : Nat} (τ : Rew language Nat n Nat m) (x y z : Term n) :
    Semiformula.rewAux τ (mulResult x y z) = mulResult (τ x) (τ y) (τ z) := by
  simp only [mulResult,Semiformula.rewAux,mulPrefix_rew,Ordinal.zero_rew,
    edge,kuratowski,singleton,pair,mem,eq,sourceIff,sourceImply,
    Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq,
    Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ,
    Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  simp only [Function.comp_def,Matrix.comp_vecCons, Rew.q_comp_bShift_app,Rew.q_bvar_zero,Rew.q_bvar_succ, Ordinal.q_q_bvar_one,Ordinal.q_q_q_bvar_two,q_q_q_q_bvar_three]
  finishSourceSyntax
#print axioms mulPrefix_rew
#print axioms mulResult_rew
end M6.PA.RelationalSource.PairGraph
