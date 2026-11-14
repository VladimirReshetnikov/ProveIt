import PA194FoundationGraphExactExistence
import PA194FoundationFormulaCongruence
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula)

def graphDomain (top g : Term n) : Formula n :=
  ∀⁰ sourceIff (∃⁰ edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
    (mem (Rew.bShift top) (.bvar 0) ⋎ eq (.bvar 0) (Rew.bShift top))
def graphFunctional (g : Term n) : Formula n :=
  ∀⁰ ∀⁰ ∀⁰ sourceImply
    (edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 1) ⋏
      edge (Rew.bShift (Rew.bShift (Rew.bShift g))) (.bvar 2) (.bvar 0))
    (eq (.bvar 1) (.bvar 0))
def graphRange (g : Term n) : Formula n :=
  ∀⁰ ∀⁰ sourceImply (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
    (Ordinal.domain (.bvar 0))
def pointGraph (a b g : Term n) : Formula n :=
  ∀⁰ ∀⁰ sourceIff (edge (Rew.bShift (Rew.bShift g)) (.bvar 1) (.bvar 0))
    (eq (.bvar 1) (Rew.bShift (Rew.bShift a)) ⋏
      eq (.bvar 0) (Rew.bShift (Rew.bShift b)))

macro "traceSyntax" : tactic => `(tactic|
  (simp only [graphDomain,graphFunctional,graphRange,pointGraph,edge,inclusion,
    kuratowskiExists,adjunction,singleton,pair,kuratowski,mem,eq,sourceIff,sourceImply,
    Ordinal.zero,Ordinal.subset,Ordinal.transitive,Ordinal.memberTransitive,Ordinal.memberLinear,
    Ordinal.nonempty,Ordinal.least,Ordinal.greatest,Ordinal.internalExtrema,Ordinal.representative,
    Ordinal.memberIr,Ordinal.domain,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def domainTransport {Γ : List Form} (E : FormulaEquality Γ) (a b : Nat)
    (hab : ND.Proof Γ (eq (.fvar a) (.fvar b)))
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (Ordinal.domain (.fvar b)) := by
  have hp : ND.Proof Γ (Semiformula.rewAux (Rew.subst ![.fvar a]) (Ordinal.domain (.bvar 0))) := by
    convert ha using 1 ; ordinalSyntax
  have h := E.substituteOne (Ordinal.domain (.bvar 0)) (.fvar a) (.fvar b) hab hp
  convert h using 1 ; ordinalSyntax

def emptyNoEdge {Γ : List Form} (g a b : Nat)
    (hz : ND.Proof Γ (Ordinal.zero (.fvar g)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar a) (.fvar b))) : ND.Proof Γ ⊥ := by
  apply exsElim he
  let σ : Formula 1 := mem (.fvar g) (.bvar 0) ⋏ kuratowski (.bvar 0) (.fvar a) (.fvar b)
  let C := σ.free :: shifted Γ
  have hm : ND.Proof C (mem (.fvar (g+1)) (.fvar 0)) := by
    have hc : ND.Proof C (mem (.fvar (g+1)) (.fvar 0) ⋏
        kuratowski (.fvar 0) (.fvar (a+1)) (.fvar (b+1))) := by
      have h : ND.Proof C σ.free := assumption (by simp [C])
      convert h using 1 ; dsimp [σ] ; graphSyntax
    exact andLeft hc
  have hn := up (Ordinal.zeroNotMem (g+1) 0 (Ordinal.zeroShift g hz)) σ.free
  convert contradiction hm hn using 1 <;> (dsimp [C,σ] <;> graphSyntax)

def pointAt {Γ : List Form} (a b g x y : Nat)
    (h : ND.Proof Γ (pointGraph (.fvar a) (.fvar b) (.fvar g))) :
    ND.Proof Γ (sourceIff (edge (.fvar g) (.fvar x) (.fvar y))
      (eq (.fvar x) (.fvar a) ⋏ eq (.fvar y) (.fvar b))) := by
  convert allElim _ (.fvar y) (allElim _ (.fvar x) h) using 1
  traceSyntax

#print axioms domainTransport
#print axioms emptyNoEdge
#print axioms pointAt
end M6.PA.RelationalSource.PairGraph

