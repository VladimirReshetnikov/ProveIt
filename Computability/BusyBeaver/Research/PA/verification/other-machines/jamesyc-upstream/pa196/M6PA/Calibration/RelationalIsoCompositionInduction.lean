module
public import M6PA.Theory
public import M6PA.Calibration.RelationalIsoCompositionGuardedStep
public import M6PA.Calibration.RelationalIsoCompositionEmpty
@[expose] public section

/-! Uniform composition-prefix construction by accepted ordinal induction.
The precise subset guard and free graph parameters are retained. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
open Ordinal (Term Formula)

def compositionProperty (g h a : Nat) : Formula 1 :=
  sourceImply (Ordinal.subset (.bvar 0) (.fvar a)) (compositionPrefixExists (.fvar g) (.fvar h) (.bvar 0))

def compositionInductionBase {Γ : List Form} (g h a : Nat) :
    ND.Proof Γ (Ordinal.inductionBase (compositionProperty g h a)) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d :: shifted Γ) d := assumption (by simp)
  have out : ND.Proof (d :: shifted Γ)
      (Ordinal.subset (.fvar 0) (.fvar (a+1)) 🡒 compositionPrefixExists (.fvar (g+1)) (.fvar (h+1)) (.fvar 0)) :=
    impIntro (up (emptyCompositionPrefixExists (g+1) (h+1) 0 (andRight hd)) _)
  convert impIntro out using 1 <;>
    (dsimp [d,Ordinal.inductionBase,compositionProperty] <;> compositionSyntax)

set_option maxHeartbeats 800000 in
def compositionInductionStep {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hh : ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar b))) :
    ND.Proof Γ (Ordinal.inductionStep (compositionProperty g h a)) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏
      (Ordinal.subset (.fvar 1) (.fvar (a+1+1)) 🡒 compositionPrefixExists (.fvar (g+1+1)) (.fvar (h+1+1)) (.fvar 1))))
  have hd : ND.Proof (d :: shifted (shifted Γ)) d := assumption (by simp)
  have out := compositionGuardedStep (E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp))
    (g+1+1) (h+1+1) (a+1+1) (b+1+1) 1 0 (up (emptyClosedShift (emptyClosedShift hempty)) d)
    (up (adjunctionClosedShift (adjunctionClosedShift hadj)) d)
    (up (orderTypedShift (g+1) (a+1) (b+1) (orderTypedShift g a b ht)) d)
    (up (orderLeftShift (g+1) (a+1) (orderLeftShift g a hg)) d)
    (up (orderLeftShift (h+1) (b+1) (orderLeftShift h b hh)) d)
    (andLeft (andRight (andRight hd))) (andRight (andRight (andRight hd)))
  convert impIntro out using 1 <;>
    (dsimp [d,Ordinal.inductionStep,Ordinal.traceProperty,compositionProperty] <;> compositionSyntax)

def compositionTotalWitness {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼compositionProperty g h a)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hh : ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar b))) :
    ND.Proof Γ (Ordinal.inductionConclusion (compositionProperty g h a)) :=
  Ordinal.uniformInduction E.core (compositionProperty g h a) E.transitive hi hadj hsep
    (compositionInductionBase g h a) (compositionInductionStep E g h a b hempty hadj ht hg hh)

def compositionFullPrefixExists {Γ : List Form} (E : FormulaEquality Γ) (g h a b : Nat)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hsep : ND.Proof Γ (separationFormula (∼compositionProperty g h a)))
    (ht : ND.Proof Γ (graphTyped (.fvar g) (.fvar a) (.fvar b)))
    (hg : ND.Proof Γ (graphLeftTotal (.fvar g) (.fvar a)))
    (hh : ND.Proof Γ (graphLeftTotal (.fvar h) (.fvar b)))
    (hd : ND.Proof Γ (Ordinal.domain (.fvar a))) :
    ND.Proof Γ (compositionPrefixExists (.fvar g) (.fvar h) (.fvar a)) := by
  have hp : ND.Proof Γ (Ordinal.domain (.fvar a) 🡒
      (Ordinal.subset (.fvar a) (.fvar a) 🡒 compositionPrefixExists (.fvar g) (.fvar h) (.fvar a))) := by
    convert allElim _ (.fvar a) (compositionTotalWitness E g h a b hempty hadj hi hsep ht hg hh) using 1 <;>
      (dsimp [Ordinal.inductionConclusion,compositionProperty] <;> compositionSyntax)
  exact mp (Ordinal.subsetReflexive a) (mp hd hp)

#print axioms compositionInductionBase
#print axioms compositionInductionStep
#print axioms compositionTotalWitness
#print axioms compositionFullPrefixExists
end M6.PA.RelationalSource.PairGraph
