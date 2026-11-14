import PA194FoundationIdentityTotalExtension

/-! Actual finite proof data for an identity graph successor construction. -/
namespace M6.PA.RelationalSource.PairGraph
open LO LO.FirstOrder ND

def identityGraphShift {Γ : List Form} (g a : Nat)
    (h : ND.Proof Γ (identityGraph (.fvar g) (.fvar a))) :
    ND.Proof (shifted Γ) (identityGraph (.fvar (g+1)) (.fvar (a+1))) := by
  convert shiftProof h using 1 <;> isoSyntax

structure IdentityFrame (Γ : List Form) (g a b : Nat) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  graph : ND.Proof Γ (identityGraph (.fvar g) (.fvar a))
  successor : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar b))

def IdentityFrame.weaken {Γ Δ : List Form} {g a b : Nat} (I : IdentityFrame Γ g a b)
    (inc : ∀ p, p ∈ Γ → p ∈ Δ) : IdentityFrame Δ g a b where
  equality := I.equality.weaken inc
  empty := ND.weaken I.empty inc
  adjunction := ND.weaken I.adjunction inc
  graph := ND.weaken I.graph inc
  successor := ND.weaken I.successor inc

def IdentityFrame.shift {Γ : List Form} {g a b : Nat} (I : IdentityFrame Γ g a b) :
    IdentityFrame (shifted Γ) (g+1) (a+1) (b+1) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  graph := identityGraphShift g a I.graph
  successor := Ordinal.successorShift a b I.successor

#print axioms identityGraphShift
#print axioms IdentityFrame.weaken
#print axioms IdentityFrame.shift
end M6.PA.RelationalSource.PairGraph
