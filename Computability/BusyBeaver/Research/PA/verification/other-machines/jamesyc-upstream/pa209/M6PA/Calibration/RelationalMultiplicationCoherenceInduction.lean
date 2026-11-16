module
public import M6PA.Theory
public import M6PA.Calibration.RelationalMultiplicationCoherenceZero
public import M6PA.Calibration.RelationalMultiplicationCoherenceStep
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! The exact minimum-counterexample ordinal induction instance for full
multiplication coherence, retaining its one negated-property Separation premise. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] mulResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

macro "mulCoherenceInductionSyntax" : tactic => `(tactic|
  (simp only [Ordinal.inductionBase,Ordinal.inductionStep,Ordinal.inductionConclusion,
    Ordinal.traceProperty,mulCoherence,mulCoherenceProperty,mulCoherencePoint,mulCoherencePremise,
    mulResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.zero_rew,Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def mulCoherenceInductionBase {Γ : List Form} (E : FormulaEquality Γ) :
    ND.Proof Γ (Ordinal.inductionBase mulCoherenceProperty) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d::shifted Γ) d := assumption (by simp)
  have out := mulCoherenceZero (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) 0 (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> mulCoherenceInductionSyntax)

def mulCoherenceInductionStep {Γ : List Form} (E : FormulaEquality Γ)
    (haddition : ND.Proof Γ addCoherenceStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (Ordinal.inductionStep mulCoherenceProperty) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ mulCoherence (.fvar 1)))
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  let I : MultiplicationCoherenceStepFrame (d::shifted (shifted Γ)) 1 0 :=
    ⟨up (additionCoherenceClosedShift (additionCoherenceClosedShift haddition)) d,
      E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp),
      up (emptyClosedShift (emptyClosedShift hempty)) d,
      up (adjunctionClosedShift (adjunctionClosedShift hadj)) d,
      up (predecessorClosedSeparationShift (predecessorClosedSeparationShift hstrict)) d,
      up (additionInclusiveSeparationShift (additionInclusiveSeparationShift hinclusive)) d,
      andLeft hd,andLeft (andRight (andRight hd)),andRight (andRight (andRight hd))⟩
  have out := mulCoherenceSuccessor 1 0 I
  convert impIntro out using 1 <;> (dsimp [d] <;> mulCoherenceInductionSyntax)

def multiplicationCoherenceConclusion {Γ : List Form} (E : FormulaEquality Γ)
    (haddition : ND.Proof Γ addCoherenceStatement)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation)
    (hsep : ND.Proof Γ (separationFormula (∼mulCoherenceProperty))) :
    ND.Proof Γ (Ordinal.inductionConclusion mulCoherenceProperty) :=
  Ordinal.uniformInduction E.core mulCoherenceProperty E.transitive hi hadj hsep
    (mulCoherenceInductionBase E) (mulCoherenceInductionStep E haddition hempty hadj hstrict hinclusive)

#print axioms mulCoherenceInductionBase
#print axioms mulCoherenceInductionStep
#print axioms multiplicationCoherenceConclusion
end M6.PA.RelationalSource.PairGraph
