module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityEmpty
@[expose] public section

/-! Finite inverse prefixes with actual graph-object witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseEntryWitness (g n p : Term k) : Formula k :=
  ∃¹ ∃¹ (mem (Rew.bShift (Rew.bShift n)) (.bvar 1) ⋏
    (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0) ⋏
      kuratowski (Rew.bShift (Rew.bShift p)) (.bvar 0) (.bvar 1)))
def inverseEntries (g n h : Term k) : Formula k :=
  ∀¹ sourceImply (mem (Rew.bShift h) (.bvar 0))
    (inverseEntryWitness (Rew.bShift g) (Rew.bShift n) (.bvar 0))
def inverseCorrect (g n h : Term k) : Formula k :=
  ∀¹ ∀¹ sourceImply
    (edge (Rew.bShift (Rew.bShift h)) (.bvar 1) (.bvar 0))
    (mem (Rew.bShift (Rew.bShift n)) (.bvar 0) ⋏
      edge (Rew.bShift (Rew.bShift g)) (.bvar 0) (.bvar 1))
def inverseCoverage (g n h : Term k) : Formula k :=
  ∀¹ sourceImply (mem (Rew.bShift n) (.bvar 0))
    (∃¹ (edge (Rew.bShift (Rew.bShift h)) (.bvar 0) (.bvar 1) ⋏
      edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0)))
def inversePrefix (g n h : Term k) : Formula k :=
  inverseEntries g n h ⋏ (inverseCorrect g n h ⋏ inverseCoverage g n h)
def inversePrefixExists (g n : Term k) : Formula k :=
  ∃¹ inversePrefix (Rew.bShift g) (Rew.bShift n) (.bvar 0)

macro "inverseSyntax" : tactic => `(tactic|
  (simp only [inverseEntryWitness,inverseEntries,inverseCorrect,inverseCoverage,inversePrefix,inversePrefixExists,entryWitness,graphEntries,graphTyped,graphLeftTotal,graphRightTotal,
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
