module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIdentityExistsStep
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! Uniform ordinal induction constructs actual identity graphs, with the
precise negated-identity-existence Separation instance still explicit here. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def identityProperty : Formula 1 := identityExists (.bvar 0)

def identityInductionBase {Γ : List Form} : ND.Proof Γ (Ordinal.inductionBase identityProperty) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out := impIntro (emptyIdentityExists 0 (andRight hd))
  convert out using 1 <;> (dsimp [d] <;> (try simp only [Ordinal.inductionBase,identityProperty]) <;> isoSyntax)

def identityInductionStep {Γ : List Form} (E : FormulaEquality Γ)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula) :
    ND.Proof Γ (Ordinal.inductionStep identityProperty) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ identityExists (.fvar 1)))
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have out := identityExistsStep (E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) 1 0
    (up (emptyClosedShift (emptyClosedShift hempty)) d)
    (up (adjunctionClosedShift (adjunctionClosedShift hadj)) d)
    (andLeft (andRight (andRight hd))) (andRight (andRight (andRight hd)))
  convert impIntro out using 1 <;>
    (dsimp [d] <;> (try simp only [Ordinal.inductionStep,Ordinal.traceProperty,identityProperty]) <;> isoSyntax)

def identityTotalWitness {Γ : List Form} (E : FormulaEquality Γ)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼identityProperty))) :
    ND.Proof Γ (Ordinal.inductionConclusion identityProperty) :=
  Ordinal.uniformInduction E.core identityProperty E.transitive hi hadj hsep
    identityInductionBase (identityInductionStep E hempty hadj)

#print axioms identityInductionBase
#print axioms identityInductionStep
#print axioms identityTotalWitness
end M6.PA.RelationalSource.PairGraph
