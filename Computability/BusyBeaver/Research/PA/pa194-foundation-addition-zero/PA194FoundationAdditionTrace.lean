import PA194FoundationPointDomain
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def addRecurrence (g : Term n) : Formula n :=
  ∀⁰ ∀⁰ ∀⁰ sourceImply
    (edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 1) ⋏
      Ordinal.successor (.bvar 0) (.bvar 2))
    (∃⁰ (edge (Rew.bShift (Rew.bShift (Rew.bShift (Rew.bShift g)))) (.bvar 1) (.bvar 0) ⋏
      Ordinal.successor (.bvar 0) (.bvar 2)))
def addPrefix (top base zero g : Term n) : Formula n :=
  graphDomain top g ⋏ (graphFunctional g ⋏ (graphRange g ⋏ (edge g zero base ⋏ addRecurrence g)))
def addResult (x y z : Term n) : Formula n :=
  ∃⁰ ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    (addPrefix (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift y)) (.bvar 1) (.bvar 0) ⋏
      edge (.bvar 0) (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift z))))
def addPrefixExists (x y : Term n) : Formula n :=
  ∃⁰ ∃⁰ (Ordinal.zero (.bvar 1) ⋏
    addPrefix (Rew.bShift (Rew.bShift x)) (Rew.bShift (Rew.bShift y)) (.bvar 1) (.bvar 0))

def zeroTransport {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.zero (.fvar a))) :
    ND.Proof Γ (Ordinal.zero (.fvar b)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar a]) (Ordinal.zero (.bvar 0))) := by
    convert ha using 1 ; ordinalSyntax
  have h := E.substituteOne (Ordinal.zero (.bvar 0)) (.fvar a) (.fvar b) hab hp
  convert h using 1 ; ordinalSyntax

def noSuccessorZero {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (ha : ND.Proof Γ (Ordinal.zero (.fvar b)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b))) : ND.Proof Γ ⊥ := by
  have hi := Ordinal.successorAt a b a hs
  have hm := mp (ND.orRight (E.reflexive (.fvar a))) (andRight hi)
  exact contradiction hm (Ordinal.zeroNotMem b a ha)

#print axioms zeroTransport
#print axioms noSuccessorZero
end M6.PA.RelationalSource.PairGraph

