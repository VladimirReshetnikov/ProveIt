module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityEmpty
@[expose] public section

/-! Literal finite composition prefixes, independently formalized against
CompositionGraph238 at commit84049b5e753190cf328cbc2d2710791ad32ad59c.
Every graph object has three real coordinate witnesses, not just typed edges. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionEdge (g h x z : Term n) : Formula n :=
  ∃¹ (edge (Rew.bShift g) (Rew.bShift x) (.bvar 0) ⋏
    edge (Rew.bShift h) (.bvar 0) (Rew.bShift z))
def compositionEntryWitness (g h n p : Term k) : Formula k :=
  ∃¹ ∃¹ ∃¹ (mem (Rew.bShift (Rew.bShift (Rew.bShift n))) (.bvar 2) ⋏
    (edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 1) ⋏
      (edge (Rew.bShift (Rew.bShift (Rew.bShift h))) (.bvar 1) (.bvar 0) ⋏
        kuratowski (Rew.bShift (Rew.bShift (Rew.bShift p))) (.bvar 2) (.bvar 0))))
def compositionEntries (g h n k : Term l) : Formula l :=
  ∀¹ sourceImply (mem (Rew.bShift k) (.bvar 0))
    (compositionEntryWitness (Rew.bShift g) (Rew.bShift h) (Rew.bShift n) (.bvar 0))
def compositionCorrect (g h n k : Term l) : Formula l :=
  ∀¹ ∀¹ sourceImply (edge (Rew.bShift (Rew.bShift k)) (.bvar 1) (.bvar 0))
    (mem (Rew.bShift (Rew.bShift n)) (.bvar 1) ⋏
      compositionEdge (Rew.bShift (Rew.bShift g)) (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0))
def compositionCoverage (g h n k : Term l) : Formula l :=
  ∀¹ sourceImply (mem (Rew.bShift n) (.bvar 0))
    (∃¹ (edge (Rew.bShift (Rew.bShift k)) (.bvar 1) (.bvar 0) ⋏
      compositionEdge (Rew.bShift (Rew.bShift g)) (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0)))
def compositionPrefix (g h n k : Term l) : Formula l :=
  compositionEntries g h n k ⋏ (compositionCorrect g h n k ⋏ compositionCoverage g h n k)
def compositionPrefixExists (g h n : Term l) : Formula l :=
  ∃¹ compositionPrefix (Rew.bShift g) (Rew.bShift h) (Rew.bShift n) (.bvar 0)

macro "compositionSyntax" : tactic => `(tactic|
  (simp only [compositionEdge,compositionEntryWitness,compositionEntries,compositionCorrect,compositionCoverage,compositionPrefix,compositionPrefixExists,entryWitness,graphEntries,graphTyped,graphLeftTotal,graphRightTotal,
    graphInjective,graphOrder,orderBijection,orderIso,identityDiagonal,identityTotal,identityGraph,identityExists,
    graphDomain,graphFunctional,graphRange,pointGraph,edge,inclusion,
    kuratowskiExists,adjunction,singleton,pair,kuratowski,mem,eq,sourceIff,sourceImply,
    Ordinal.zero,Ordinal.subset,Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,
    Ordinal.nonempty,Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

end M6.PA.RelationalSource.PairGraph
