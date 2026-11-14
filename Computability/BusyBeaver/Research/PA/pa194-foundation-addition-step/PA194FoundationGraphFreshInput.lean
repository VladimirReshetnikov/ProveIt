import PA194FoundationGraphOperations
import PA194FoundationOrdinalGraphOrder

/-! An ordinal successor is absent from a trace whose inclusive domain ends at
its predecessor. This pays the freshness premise used in graph extension. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND
open Ordinal (Term Formula EqualityProofs)

def graphDomainShift {Γ : List Form} (a g : Nat)
    (h : ND.Proof Γ (graphDomain (.fvar a) (.fvar g))) :
    ND.Proof (shifted Γ) (graphDomain (.fvar (a+1)) (.fvar (g+1))) := by
  convert shiftProof h using 1 ; traceSyntax

def graphFunctionalShift {Γ : List Form} (g : Nat)
    (h : ND.Proof Γ (graphFunctional (.fvar g))) :
    ND.Proof (shifted Γ) (graphFunctional (.fvar (g+1))) := by
  convert shiftProof h using 1 ; traceSyntax

def noOutputShift {Γ : List Form} (g a : Nat)
    (h : ND.Proof Γ (hasOutput (.fvar g) (.fvar a)).neg) :
    ND.Proof (shifted Γ) (hasOutput (.fvar (g+1)) (.fvar (a+1))).neg := by
  convert shiftProof h using 1 <;> (dsimp only [hasOutput] <;> traceSyntax)

def outputSuccessorFalse {Γ : List Form} (e : EqualityProofs Γ) (a u g : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar u)))
    (hd : ND.Proof Γ (graphDomain (.fvar a) (.fvar g)))
    (he : ND.Proof Γ (hasOutput (.fvar g) (.fvar u))) : ND.Proof Γ ⊥ := by
  apply exsElim he
  let σ : Formula 1 := edge (.fvar g) (.fvar u) (.bvar 0)
  let C := σ.free :: shifted Γ
  have hm : ND.Proof C (edge (.fvar (g+1)) (.fvar (u+1)) (.fvar 0)) := by
    have h : ND.Proof C σ.free := assumption (by simp [C])
    convert h using 1 ; dsimp [σ]; traceSyntax
  have hi := graphDomainAt (a+1) (g+1) (u+1) (up (graphDomainShift a g hd) σ.free)
  have hx := mp (outputIntro (g+1) (u+1) 0 hm) (andLeft hi)
  have out := successorFresh (e.shift.up σ.free) (a+1) (u+1)
    (up (domainShift a ha) σ.free) (up (Ordinal.successorShift a u hs) σ.free) hx
  convert out using 1 <;> (dsimp [C,σ] <;> traceSyntax)

def noOutputSuccessor {Γ : List Form} (e : EqualityProofs Γ) (a u g : Nat)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hs : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar u)))
    (hd : ND.Proof Γ (graphDomain (.fvar a) (.fvar g))) :
    ND.Proof Γ (hasOutput (.fvar g) (.fvar u)).neg := by
  apply byContradiction
  let q : Form := (hasOutput (.fvar g) (.fvar u)).neg.neg
  have he : ND.Proof (q::Γ) (hasOutput (.fvar g) (.fvar u)) := assumption (by simp [q,Semiformula.neg_neg])
  exact outputSuccessorFalse (e.up q) a u g (up ha q) (up hs q) (up hd q) he

#print axioms outputSuccessorFalse
#print axioms noOutputSuccessor
end M6.PA.RelationalSource.PairGraph
