module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionZeroExistence
@[expose] public section

/-! Literal multiplication trace clauses. The base edge is (zero, zero).
The second argument is fixed in the backwards additive recurrence. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def mulRecurrence (g base : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ sourceImply
    (edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 1) ⋏
      Ordinal.successor (.bvar 0) (.bvar 2))
    (∃¹ (edge (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift g)))) (.bvar 1) (.bvar 0) ⋏
      addResult (.bvar 0) (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift base)))) (.bvar 2)))
def mulPrefix (top base zero g : Term n) : Formula n :=
  graphDomain top g ⋏ (graphFunctional g ⋏ (graphRange g ⋏ (edge g zero zero ⋏ mulRecurrence g base)))
def mulResult (x y z : Term n) : Formula n :=
  ∃¹ ∃¹ (Ordinal.zero (.bvar 1) ⋏
    (mulPrefix (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift y)) (.bvar 1) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift z))))
def mulPrefixExists (x y : Term n) : Formula n :=
  ∃¹ ∃¹ (Ordinal.zero (.bvar 1) ⋏
    mulPrefix (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift y)) (.bvar 1) (.bvar 0))
def mulTotalProperty (x : Term n) : Formula n :=
  ∀¹ sourceImply (Ordinal.domain (.bvar 0)) (mulPrefixExists (Rew.bShift x) (.bvar 0))

macro "mulSyntax" : tactic => `(tactic|
  (simp only [mulTotalProperty,mulPrefixExists,mulPrefix,mulRecurrence,mulResult,addPrefixExists,addPrefix,addRecurrence,addResult,Ordinal.successor,graphDomain,graphFunctional,graphRange,pointGraph,edge,inclusion,
    kuratowskiExists,adjunction,singleton,pair,kuratowski,mem,eq,sourceIff,sourceImply,
    Ordinal.zero,Ordinal.subset,Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,
    Ordinal.nonempty,Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

end M6.PA.RelationalSource.PairGraph

