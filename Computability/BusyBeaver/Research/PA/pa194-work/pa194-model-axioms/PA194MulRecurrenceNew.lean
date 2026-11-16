import PA194MulAddResultTransport
import PA194FoundationAdditionRecurrenceExtension
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
namespace PA194MulRecurrenceNew
open LO LO.FirstOrder
open scoped LO.FirstOrder
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph
open PA194MulAddResultTransport PA194ForwardMulZero
attribute [local irreducible] addResult

def mulPrevious {n : Nat} (g base z y : Term n) : Formula n :=
  ∃⁰ (edge (Rew.bShift g) (Rew.bShift z) (.bvar 0) ⋏
    addResult (.bvar 0) (Rew.bShift base) (Rew.bShift y))

def previousIntro {Γ : List Form} (g base z y c : Nat)
    (he : ND.Proof Γ (edge (.fvar g) (.fvar z) (.fvar c)))
    (ha : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar y))) :
    ND.Proof Γ (mulPrevious (.fvar g) (.fvar base) (.fvar z) (.fvar y)) := by
  apply ND.exsIntro _ (.fvar c)
  convert ND.andIntro he ha using 1 <;>
    simp [mulPrevious,Semiformula.rewAux,edge_rew,addResult_rew,Rew.subst,Rew.q,Rew.func]

def newCase {Γ : List Form} (E : FormulaEquality Γ)
    (top u c v g h base x y z : Nat)
    (hu : ND.Proof Γ (Ordinal.domain (.fvar u)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar top) (.fvar u)))
    (hend : ND.Proof Γ (edge (.fvar g) (.fvar top) (.fvar c)))
    (hext : ND.Proof Γ (exactExtension (.fvar g) (.fvar h) (.fvar u) (.fvar v)))
    (hadd : ND.Proof Γ (addResult (.fvar c) (.fvar base) (.fvar v)))
    (hxu : ND.Proof Γ (eq (.fvar x) (.fvar u)))
    (hyv : ND.Proof Γ (eq (.fvar y) (.fvar v)))
    (hzx : ND.Proof Γ (Ordinal.successor (.fvar z) (.fvar x))) :
    ND.Proof Γ (mulPrevious (.fvar h) (.fvar base) (.fvar z) (.fvar y)) := by
  have hzu := successorTargetTransport E z x u hxu hzx
  have hzt := successorPredecessorUnique E.core u z top hu hzu hs
  have he := edgeInputTransport E g top z c (E.symmetryOf hzt) hend
  have hh := exactPreservesEdge g h u v z c hext he
  have ha := outputTransport E c base v y (E.symmetryOf hyv) hadd
  exact previousIntro h base z y c hh ha
#print axioms previousIntro
#print axioms newCase
end PA194MulRecurrenceNew
