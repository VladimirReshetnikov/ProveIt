module
public import M6PA.Theory
public import M6PA.Calibration.RelationalTraceGraph
@[expose] public section

/-! Existential order-isomorphisms of nonextensional ordinal representatives.
All seven clauses are explicit, including actual Kuratowski witnesses for every
object in the graph. Mathematical interface: pinned IsoGraph238; no proof text
is ported and no canonical representatives or extensionality are assumed. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def entryWitness (a b p : Term n) : Formula n :=
  ∃¹ ∃¹ (mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏
    (mem (Rew.bShift (Rew.bShift b)) (.bvar 0) ⋏
      kuratowski (Rew.bShift (Rew.bShift p)) (.bvar 1) (.bvar 0)))
def graphEntries (g a b : Term n) : Formula n :=
  ∀¹ sourceImply (mem (Rew.bShift g) (.bvar 0))
    (entryWitness (Rew.bShift a) (Rew.bShift b) (.bvar 0))
def graphTyped (g a b : Term n) : Formula n :=
  ∀¹ ∀¹ sourceImply (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
    (mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏ mem (Rew.bShift (Rew.bShift b)) (.bvar 0))
def graphLeftTotal (g a : Term n) : Formula n :=
  ∀¹ sourceImply (mem (Rew.bShift a) (.bvar 0))
    (∃¹ edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
def graphRightTotal (g b : Term n) : Formula n :=
  ∀¹ sourceImply (mem (Rew.bShift b) (.bvar 0))
    (∃¹ edge (Rew.bShift (Rew.bShift g)) (.bvar 0) (.bvar 1))
def graphInjective (g : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ sourceImply
    (edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 0) ⋏
      edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 1) (.bvar 0))
    (eq (.bvar 2) (.bvar 1))
def graphOrder (g : Term n) : Formula n :=
  ∀¹ ∀¹ ∀¹ ∀¹ sourceImply
    (edge (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift g)))) (.bvar 3) (.bvar 1) ⋏
      edge (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift g)))) (.bvar 2) (.bvar 0))
    (sourceIff (mem (.bvar 3) (.bvar 2)) (mem (.bvar 1) (.bvar 0)))
def orderBijection (g a b : Term n) : Formula n :=
  graphEntries g a b ⋏ (graphTyped g a b ⋏ (graphLeftTotal g a ⋏
    (graphRightTotal g b ⋏ (graphFunctional g ⋏ (graphInjective g ⋏ graphOrder g)))))
def orderIso (a b : Term n) : Formula n :=
  ∃¹ orderBijection (.bvar 0) (Rew.bShift a) (Rew.bShift b)

def identityDiagonal (g a : Term n) : Formula n :=
  ∀¹ ∀¹ sourceImply (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
    (mem (Rew.bShift (Rew.bShift a)) (.bvar 1) ⋏ eq (.bvar 1) (.bvar 0))
def identityTotal (g a : Term n) : Formula n :=
  ∀¹ sourceImply (mem (Rew.bShift a) (.bvar 0)) (edge (Rew.bShift g) (.bvar 0) (.bvar 0))
def identityGraph (g a : Term n) : Formula n :=
  graphEntries g a a ⋏ (identityDiagonal g a ⋏ identityTotal g a)
def identityExists (a : Term n) : Formula n :=
  ∃¹ identityGraph (.bvar 0) (Rew.bShift a)

macro "isoSyntax" : tactic => `(tactic|
  (simp only [entryWitness,graphEntries,graphTyped,graphLeftTotal,graphRightTotal,
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

