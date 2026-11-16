module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionRightZero
@[expose] public section

/-! Uniform ordinal induction for the universally parameterized right-zero law. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def addRightZeroInductionBase {Γ : List Form} (E : FormulaEquality Γ) :
    ND.Proof Γ (Ordinal.inductionBase addRightZeroProperty) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d::shifted Γ) d := assumption (by simp)
  have out := addRightZeroBase (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) 0 (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> addRightZeroSyntax)

def addRightZeroInductionStep {Γ : List Form} (E : FormulaEquality Γ)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (Ordinal.inductionStep addRightZeroProperty) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ addRightZero (.fvar 1)))
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  let I : AdditionRightZeroFrame (d::shifted (shifted Γ)) 1 0 :=
    ⟨E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp),
      up (emptyClosedShift (emptyClosedShift hempty)) d,
      up (adjunctionClosedShift (adjunctionClosedShift hadj)) d,
      up (additionInclusiveSeparationShift (additionInclusiveSeparationShift hinclusive)) d,
      andLeft hd,andLeft (andRight (andRight hd)),andRight (andRight (andRight hd))⟩
  have out := addRightZeroSuccessor 1 0 I
  convert impIntro out using 1 <;> (dsimp [d] <;> addRightZeroSyntax)

def additionRightZeroConclusion {Γ : List Form} (E : FormulaEquality Γ)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation)
    (hsep : ND.Proof Γ (separationFormula (∼addRightZeroProperty))) :
    ND.Proof Γ (Ordinal.inductionConclusion addRightZeroProperty) :=
  Ordinal.uniformInduction E.core addRightZeroProperty E.transitive hi hadj hsep
    (addRightZeroInductionBase E) (addRightZeroInductionStep E hempty hadj hinclusive)

#print axioms addRightZeroInductionBase
#print axioms addRightZeroInductionStep
#print axioms additionRightZeroConclusion
end M6.PA.RelationalSource.PairGraph
