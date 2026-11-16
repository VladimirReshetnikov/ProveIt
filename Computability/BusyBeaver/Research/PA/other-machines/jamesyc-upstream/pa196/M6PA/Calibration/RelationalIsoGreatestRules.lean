module
public import M6PA.Theory
public import M6PA.Calibration.RelationalOrderIsoRelationRules
public import M6PA.Calibration.RelationalOrdinalInductionPredecessor
public import M6PA.Calibration.RelationalGraphOperations
@[expose] public section

/-! A successor endpoint is greatest; an order-bijection transports its
comparison property through actual graph edges. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND

def successorGreatest {Γ : List Form} (E : Ordinal.EqualityProofs Γ) (p a : Nat)
    (hs : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar a))) :
    ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar p)) := by
  have hm := mp (ND.orRight (Ordinal.eqRefl E p)) (andRight (Ordinal.successorAt p a p hs))
  apply andIntro hm
  apply allIntro
  let premise : Form := mem (.fvar (a+1)) (.fvar 0)
  have hx : ND.Proof (premise::shifted Γ) premise := assumption (by simp)
  have hd := mp hx (andLeft (Ordinal.successorAt (p+1) (a+1) 0
    (up (Ordinal.successorShift p a hs) premise)))
  have out : ND.Proof (premise::shifted Γ)
      (eq (.fvar 0) (.fvar (p+1)) ⋎ mem (.fvar (p+1)) (.fvar 0)) := by
    apply orElim hd
    · exact ND.orRight (assumption (by simp))
    · exact ND.orLeft (assumption (by simp))
  convert impIntro out using 1 <;> (dsimp [premise] <;> isoSyntax)

def imageGreatestEdge {Γ : List Form} (E : FormulaEquality Γ) (g a b p q x y : Nat)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hf : ND.Proof Γ (graphFunctional (.fvar g)))
    (ho : ND.Proof Γ (graphOrder (.fvar g)))
    (hp : ND.Proof Γ (Ordinal.greatest (.fvar a) (.fvar p)))
    (he : ND.Proof Γ (edge (.fvar g) (.fvar p) (.fvar q)))
    (hx : ND.Proof Γ (edge (.fvar g) (.fvar x) (.fvar y))) :
    ND.Proof Γ (eq (.fvar y) (.fvar q) ⋎ mem (.fvar q) (.fvar y)) := by
  have ha := andLeft (orderTypedAt g a b x y ht hx)
  apply orElim (Ordinal.greatestAt a p x hp ha)
  · let premise : Form := eq (.fvar x) (.fvar p)
    let EE := E.weaken (fun r hr => List.mem_cons_of_mem premise hr)
    have changed := edgeInputTransport EE g x p y (assumption (by simp [premise])) (up hx premise)
    exact ND.orLeft (graphFunctionalAt g p y q (up hf premise) changed (up he premise))
  · let premise : Form := mem (.fvar p) (.fvar x)
    have horder := orderOrderAt g p x q y (up ho premise) (up he premise) (up hx premise)
    exact ND.orRight (mp (assumption (by simp [premise])) (andLeft horder))

#print axioms successorGreatest
#print axioms imageGreatestEdge
end M6.PA.RelationalSource.PairGraph
