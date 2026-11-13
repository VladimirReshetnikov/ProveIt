module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativity
@[expose] public section

/-! Explicit finite proof inputs for commutativity; closed totality is consumed
only to obtain real existential witnesses. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000

structure AdditionCommutativityBasis (Γ : List Form) where
  equality : FormulaEquality Γ
  empty : ND.Proof Γ emptyFormula
  adjunction : ND.Proof Γ adjunctionFormula
  intersection : ND.Proof Γ Ordinal.intersectionFormula
  separation : ND.Proof Γ closedInclusiveSeparation
  rightZero : ND.Proof Γ addRightZeroStatement
  rightSuccessor : ND.Proof Γ addRightSuccessorStatement
  transitivity : ND.Proof Γ isoTransitivityClosed
  addition : ND.Proof Γ addClosedResult
  successor : ND.Proof Γ ForwardRelational.successorClosed

def AdditionCommutativityBasis.weaken {Γ Δ : List Form}
    (I : AdditionCommutativityBasis Γ) (inc : ∀ p,p∈Γ→p∈Δ) : AdditionCommutativityBasis Δ :=
  ⟨I.equality.weaken inc,ND.weaken I.empty inc,ND.weaken I.adjunction inc,
    ND.weaken I.intersection inc,ND.weaken I.separation inc,ND.weaken I.rightZero inc,
    ND.weaken I.rightSuccessor inc,ND.weaken I.transitivity inc,
    ND.weaken I.addition inc,ND.weaken I.successor inc⟩

def AdditionCommutativityBasis.shift {Γ : List Form} (I : AdditionCommutativityBasis Γ) :
    AdditionCommutativityBasis (shifted Γ) where
  equality := I.equality.shifted
  empty := emptyClosedShift I.empty
  adjunction := adjunctionClosedShift I.adjunction
  intersection := Ordinal.intersectionAxiomShift I.intersection
  separation := additionInclusiveSeparationShift I.separation
  rightZero := addRightZeroClosedShift I.rightZero
  rightSuccessor := by
    convert shiftProof I.rightSuccessor using 1 <;>
      ((try simp only [addRightSuccessorStatement]) <;> addRightSuccessorSyntax)
  transitivity := by
    convert shiftProof I.transitivity using 1 <;>
      ((try simp only [isoTransitivityClosed_eq]) <;> addCommutativitySyntax)
  addition := by
    convert shiftProof I.addition using 1 <;>
      ((try simp only [addClosedResult,closeParameter,addTotalStatement,addOutputConclusion,addOutput]) <;>
        totalitySyntax)
  successor := by
    convert shiftProof I.successor using 1 <;>
      ((try simp only [ForwardRelational.successorClosed,closeParameter,
        Ordinal.domainSuccessorStatement,Ordinal.domainSuccessorExists]) <;>
        totalitySyntax)

def AdditionCommutativityBasis.addAt {Γ : List Form} (I : AdditionCommutativityBasis Γ)
    (x y : Nat) (hx : ND.Proof Γ (Ordinal.domain (.fvar x)))
    (hy : ND.Proof Γ (Ordinal.domain (.fvar y))) : ND.Proof Γ (addOutput (.fvar x) (.fvar y)) := by
  have hh := specializeParameter (addTotalStatement 0) (.fvar y) I.addition
  have hp : ND.Proof Γ (Ordinal.domain (.fvar y) 🡒
      ∀¹ (Ordinal.domain (.bvar 0) 🡒 addOutput (.bvar 0) (.fvar y))) := by
    convert hh using 1 <;>
      ((try simp only [addTotalStatement,addOutputConclusion,addOutput]) <;> totalitySyntax)
  apply mp hx
  convert allElim _ (.fvar x) (mp hy hp) using 1 <;>
    ((try simp only [addOutput]) <;> totalitySyntax)

def AdditionCommutativityBasis.successorAt {Γ : List Form} (I : AdditionCommutativityBasis Γ)
    (x : Nat) (hx : ND.Proof Γ (Ordinal.domain (.fvar x))) :
    ND.Proof Γ (Ordinal.domainSuccessorExists (.fvar x)) := by
  have hh := specializeParameter (Ordinal.domainSuccessorStatement (.fvar 0)) (.fvar x) I.successor
  apply mp hx
  convert hh using 1 <;>
    ((try simp only [Ordinal.domainSuccessorStatement,Ordinal.domainSuccessorExists]) <;>
      totalitySyntax)

structure AdditionCommutativityFrame (Γ : List Form) (p x y : Nat) where
  basis : AdditionCommutativityBasis Γ
  hypothesis : ND.Proof Γ (addCommutativity (.fvar p))
  previousDomain : ND.Proof Γ (Ordinal.domain (.fvar p))
  baseDomain : ND.Proof Γ (Ordinal.domain (.fvar y))
  next : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))

def AdditionCommutativityFrame.weaken {Γ Δ : List Form} {p x y : Nat}
    (I : AdditionCommutativityFrame Γ p x y) (inc : ∀ q,q∈Γ→q∈Δ) :
    AdditionCommutativityFrame Δ p x y :=
  ⟨I.basis.weaken inc,ND.weaken I.hypothesis inc,ND.weaken I.previousDomain inc,
    ND.weaken I.baseDomain inc,ND.weaken I.next inc⟩

def AdditionCommutativityFrame.shift {Γ : List Form} {p x y : Nat}
    (I : AdditionCommutativityFrame Γ p x y) :
    AdditionCommutativityFrame (shifted Γ) (p+1) (x+1) (y+1) :=
  ⟨I.basis.shift,addCommutativityShift p I.hypothesis,Ordinal.domainShift p I.previousDomain,
    Ordinal.domainShift y I.baseDomain,Ordinal.successorShift p x I.next⟩

def additionCommutativityConcrete {Γ : List Form} (p x y a q v r s : Nat)
    (I : AdditionCommutativityFrame Γ p x y)
    (ha : ND.Proof Γ (Ordinal.domain (.fvar a)))
    (hq : ND.Proof Γ (Ordinal.domain (.fvar q)))
    (hpa : ND.Proof Γ (addResult (.fvar p) (.fvar y) (.fvar a)))
    (hyq : ND.Proof Γ (addResult (.fvar y) (.fvar p) (.fvar q)))
    (har : ND.Proof Γ (Ordinal.successor (.fvar a) (.fvar r)))
    (hqv : ND.Proof Γ (Ordinal.successor (.fvar q) (.fvar v)))
    (hys : ND.Proof Γ (addResult (.fvar y) (.fvar x) (.fvar s))) :
    ND.Proof Γ (orderIso (.fvar r) (.fvar s)) := by
  have lower := mp (andIntro I.baseDomain (andIntro hpa hyq))
    (addCommutativityAt p y a q I.hypothesis)
  have left := orderIsoSuccessor I.basis.equality a q r v I.basis.empty I.basis.adjunction
    ha hq har hqv lower
  have hx := Ordinal.successorDomain I.basis.equality.core I.basis.equality.transitive
    I.basis.intersection (.fvar p) (.fvar x) I.previousDomain I.next
  have right := additionRightSuccessorApply y p x q s v I.basis.rightSuccessor
    I.baseDomain I.previousDomain hx hq I.next hyq hys hqv
  have hr := Ordinal.successorDomain I.basis.equality.core I.basis.equality.transitive
    I.basis.intersection (.fvar a) (.fvar r) ha har
  exact isoTransitivityClosedAt r v s I.basis.transitivity hr left right

#print axioms AdditionCommutativityBasis.shift
#print axioms AdditionCommutativityBasis.addAt
#print axioms AdditionCommutativityFrame.shift
#print axioms additionCommutativityConcrete
end M6.PA.RelationalSource.PairGraph
