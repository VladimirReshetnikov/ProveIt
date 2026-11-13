module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoInverseGuardedStep
@[expose] public section

/-! Parameter-preserving ordinal induction with the explicit subset guard. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def inverseProperty (g a : Nat) : Formula 1 :=
  sourceImply (Ordinal.subset (.bvar 0) (.fvar a)) (inversePrefixExists (.fvar g) (.bvar 0))

def inverseInductionBase {Γ : List Form} (g a : Nat) :
    ND.Proof Γ (Ordinal.inductionBase (inverseProperty g a)) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out : ND.Proof (d :: shifted Γ)
      (Ordinal.subset (.fvar 0) (.fvar (a+1)) 🡒 inversePrefixExists (.fvar (g+1)) (.fvar 0)) :=
    impIntro (up (emptyInversePrefixExists (g+1) 0 (andRight hd)) _)
  convert impIntro out using 1 <;>
    (dsimp [d,Ordinal.inductionBase,inverseProperty] <;> inverseSyntax)

def inverseInductionStep {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (ht : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a))) :
    ND.Proof Γ (Ordinal.inductionStep (inverseProperty g a)) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏
      (Ordinal.subset (.fvar 1) (.fvar (a+1+1)) 🡒 inversePrefixExists (.fvar (g+1+1)) (.fvar 1))))
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have out := inverseGuardedStep (E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp))
    (g+1+1) (a+1+1) 1 0 (up (emptyClosedShift (emptyClosedShift hempty)) d)
    (up (adjunctionClosedShift (adjunctionClosedShift hadj)) d)
    (up (orderLeftShift (g+1) (a+1) (orderLeftShift g a ht)) d)
    (andLeft (andRight (andRight hd))) (andRight (andRight (andRight hd)))
  convert impIntro out using 1 <;>
    (dsimp [d,Ordinal.inductionStep,Ordinal.traceProperty,inverseProperty] <;> inverseSyntax)

def inverseTotalWitness {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼inverseProperty g a)))
    (ht : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a))) :
    ND.Proof Γ (Ordinal.inductionConclusion (inverseProperty g a)) :=
  Ordinal.uniformInduction E.core (inverseProperty g a) E.transitive hi hadj hsep
    (inverseInductionBase g a) (inverseInductionStep E g a hempty hadj ht)

def inverseFullPrefixExists {Γ : List Form} (E : FormulaEquality Γ) (g a : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼inverseProperty g a)))
    (ht : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (inversePrefixExists (.fvar g) (.fvar a)) := by
  have hh : ND.Proof Γ (Ordinal.domain (.fvar a) 🡒
      (Ordinal.subset (.fvar a) (.fvar a) 🡒 inversePrefixExists (.fvar g) (.fvar a))) := by
    convert allElim _ (.fvar a) (inverseTotalWitness E g a hempty hadj hi hsep ht) using 1 <;>
      (dsimp [Ordinal.inductionConclusion,inverseProperty] <;> inverseSyntax)
  exact mp (Ordinal.subsetReflexive a) (mp hd hh)

#print axioms inverseInductionBase
#print axioms inverseInductionStep
#print axioms inverseTotalWitness
#print axioms inverseFullPrefixExists
end M6.PA.RelationalSource.PairGraph
