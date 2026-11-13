module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightSuccessorStep
@[expose] public section

/-! Constructive uniform ordinal induction, with its precise negated-property
Separation assumption displayed rather than implicitly generalized. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightSuccessorInductionBase {Γ : List Form} (I : AdditionRightSuccessorBasis Γ) :
    ND.Proof Γ (Ordinal.inductionBase addRightSuccessorProperty) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d::shifted Γ) d := assumption (by simp)
  have out := addRightSuccessorBase (I.shift.weaken (fun p hp => List.mem_cons_of_mem d hp)) 0 (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> addRightSuccessorSyntax)

def addRightSuccessorInductionStep {Γ : List Form} (I : AdditionRightSuccessorBasis Γ) :
    ND.Proof Γ (Ordinal.inductionStep addRightSuccessorProperty) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ addRightSuccessor (.fvar 1)))
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  let J : AdditionRightSuccessorStepFrame (d::shifted (shifted Γ)) 1 0 :=
    ⟨I.shift.shift.weaken (fun p hp => List.mem_cons_of_mem d hp),
      andLeft hd,andLeft (andRight (andRight hd)),andRight (andRight (andRight hd))⟩
  have out := addRightSuccessorStep 1 0 J
  convert impIntro out using 1 <;> (dsimp [d] <;> addRightSuccessorSyntax)

def additionRightSuccessorConclusion {Γ : List Form} (I : AdditionRightSuccessorBasis Γ)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼addRightSuccessorProperty))) :
    ND.Proof Γ (Ordinal.inductionConclusion addRightSuccessorProperty) :=
  Ordinal.uniformInduction I.equality.core addRightSuccessorProperty I.equality.transitive hi I.adjunction hsep
    (addRightSuccessorInductionBase I) (addRightSuccessorInductionStep I)

#print axioms addRightSuccessorInductionBase
#print axioms addRightSuccessorInductionStep
#print axioms additionRightSuccessorConclusion
end M6.PA.RelationalSource.PairGraph
