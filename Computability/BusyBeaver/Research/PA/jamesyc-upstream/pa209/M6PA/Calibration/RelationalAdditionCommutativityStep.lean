module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativityOutputs
@[expose] public section

/-! Universal parameter closure of the successor step. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

structure AdditionCommutativityStepFrame (Γ : List Form) (p x : Nat) where
  basis : AdditionCommutativityBasis Γ
  hypothesis : ND.Proof Γ (addCommutativity (.fvar p))
  previousDomain : ND.Proof Γ (Ordinal.domain (.fvar p))
  next : ND.Proof Γ (Ordinal.successor (.fvar p) (.fvar x))

def AdditionCommutativityStepFrame.shift {Γ : List Form} {p x : Nat}
    (I : AdditionCommutativityStepFrame Γ p x) :
    AdditionCommutativityStepFrame (shifted Γ) (p+1) (x+1) :=
  ⟨I.basis.shift,addCommutativityShift p I.hypothesis,Ordinal.domainShift p I.previousDomain,
    Ordinal.successorShift p x I.next⟩

def addCommutativityStepPoint {Γ : List Form} (p x y r s : Nat)
    (I : AdditionCommutativityStepFrame Γ p x) :
    ND.Proof Γ (addCommutativityPoint (.fvar x) (.fvar y) (.fvar r) (.fvar s)) := by
  apply impIntro
  let d : Form := addCommutativityPremise (.fvar x) (.fvar y) (.fvar r) (.fvar s)
  have hd : ND.Proof (d::Γ) d := assumption (by simp)
  let J : AdditionCommutativityFrame (d::Γ) p x y :=
    ⟨I.basis.weaken (fun q hq => List.mem_cons_of_mem d hq),up I.hypothesis d,
      up I.previousDomain d,andLeft hd,up I.next d⟩
  exact additionCommutativityOutputs p x y r s J (andLeft (andRight hd)) (andRight (andRight hd))

def addCommutativityStep {Γ : List Form} (p x : Nat)
    (I : AdditionCommutativityStepFrame Γ p x) :
    ND.Proof Γ (addCommutativity (.fvar x)) := by
  apply allIntro
  apply allIntro
  apply allIntro
  have out := addCommutativityStepPoint (p+1+1+1) (x+1+1+1) 2 1 0 I.shift.shift.shift
  convert out using 1 <;> addCommutativitySyntax

#print axioms addCommutativityStepPoint
#print axioms addCommutativityStep
end M6.PA.RelationalSource.PairGraph
