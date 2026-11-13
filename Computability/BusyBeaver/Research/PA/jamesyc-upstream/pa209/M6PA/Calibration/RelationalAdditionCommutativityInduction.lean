module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCommutativityStep
@[expose] public section

/-! Constructive ordinal induction for addition commutativity. All auxiliary
right laws and closed witness-producing totality remain explicit finite inputs. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addCommutativityInductionBase {Γ : List Form} (I : AdditionCommutativityBasis Γ) :
    ND.Proof Γ (Ordinal.inductionBase addCommutativityProperty) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d::shifted Γ) d := assumption (by simp)
  let J := I.shift.weaken (fun p hp => List.mem_cons_of_mem d hp)
  have out := addCommutativityBase J.equality J.rightZero 0 (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> addCommutativitySyntax)

def addCommutativityInductionStep {Γ : List Form} (I : AdditionCommutativityBasis Γ) :
    ND.Proof Γ (Ordinal.inductionStep addCommutativityProperty) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ addCommutativity (.fvar 1)))
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  let J : AdditionCommutativityStepFrame (d::shifted (shifted Γ)) 1 0 :=
    ⟨I.shift.shift.weaken (fun p hp => List.mem_cons_of_mem d hp),
      andRight (andRight (andRight hd)),andLeft hd,andLeft (andRight (andRight hd))⟩
  have out := addCommutativityStep 1 0 J
  convert impIntro out using 1 <;> (dsimp [d] <;> addCommutativitySyntax)

def additionCommutativityConclusion {Γ : List Form} (I : AdditionCommutativityBasis Γ)
    (hsep : ND.Proof Γ (separationFormula (∼addCommutativityProperty))) :
    ND.Proof Γ (Ordinal.inductionConclusion addCommutativityProperty) :=
  Ordinal.uniformInduction I.equality.core addCommutativityProperty I.equality.transitive
    I.intersection I.adjunction hsep (addCommutativityInductionBase I) (addCommutativityInductionStep I)

#print axioms addCommutativityInductionBase
#print axioms addCommutativityInductionStep
#print axioms additionCommutativityConclusion
end M6.PA.RelationalSource.PairGraph
