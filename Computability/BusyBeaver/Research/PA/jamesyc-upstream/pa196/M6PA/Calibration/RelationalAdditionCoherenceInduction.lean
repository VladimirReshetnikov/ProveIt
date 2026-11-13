module
public import M6PA.Theory
public import M6PA.Calibration.RelationalAdditionCoherenceZero
public import M6PA.Calibration.RelationalAdditionCoherenceStep
public import M6PA.Calibration.RelationalOrdinalInductionUniform
@[expose] public section

/-! The exact minimum-counterexample ordinal induction instance for full
addition coherence, retaining its one negated-property Separation premise. -/
namespace M6.PA.RelationalSource.PairGraph
open FFL FFL.FirstOrder ND
attribute [local irreducible] addResult orderIso Ordinal.domain Ordinal.successor Ordinal.zero
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

macro "coherenceInductionSyntax" : tactic => `(tactic|
  (simp only [Ordinal.inductionBase,Ordinal.inductionStep,Ordinal.inductionConclusion,
    Ordinal.traceProperty,addCoherence,addCoherenceProperty,addCoherencePoint,addCoherencePremise,
    addResult_rew,orderIso_rew,Ordinal.domain_rew,Ordinal.zero_rew,Ordinal.successor_rew,coherenceRewNeg,
    Semiformula.shift,Semiformula.free,Rewriting.shift,Rewriting.free,Rewriting.subst,
    app_eq_rewAux,Semiformula.rewAux,Semiformula.neg,Semiformula.imp_eq,Semiformula.neg_eq];
    finishSourceSyntax))

def addCoherenceInductionBase {Γ : List Form} (E : FormulaEquality Γ) :
    ND.Proof Γ (Ordinal.inductionBase addCoherenceProperty) := by
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 0) ⋏ Ordinal.zero (.fvar 0)
  have hd : ND.Proof (d::shifted Γ) d := assumption (by simp)
  have out := addCoherenceZero (E.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp)) 0 (andRight hd)
  convert impIntro out using 1 <;> (dsimp [d] <;> coherenceInductionSyntax)

def addCoherenceInductionStep {Γ : List Form} (E : FormulaEquality Γ)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation) :
    ND.Proof Γ (Ordinal.inductionStep addCoherenceProperty) := by
  apply allIntro
  apply allIntro
  let d : Form := Ordinal.domain (.fvar 1) ⋏ (Ordinal.domain (.fvar 0) ⋏
    (Ordinal.successor (.fvar 1) (.fvar 0) ⋏ addCoherence (.fvar 1)))
  have hd : ND.Proof (d::shifted (shifted Γ)) d := assumption (by simp)
  let I : AdditionCoherenceStepFrame (d::shifted (shifted Γ)) 1 0 :=
    ⟨E.shifted.shifted.weaken (fun p hp => List.mem_cons_of_mem d hp),
      up (emptyClosedShift (emptyClosedShift hempty)) d,
      up (adjunctionClosedShift (adjunctionClosedShift hadj)) d,
      up (predecessorClosedSeparationShift (predecessorClosedSeparationShift hstrict)) d,
      up (additionInclusiveSeparationShift (additionInclusiveSeparationShift hinclusive)) d,
      andLeft hd,andLeft (andRight (andRight hd)),andRight (andRight (andRight hd))⟩
  have out := addCoherenceSuccessor 1 0 I
  convert impIntro out using 1 <;> (dsimp [d] <;> coherenceInductionSyntax)

def additionCoherenceConclusion {Γ : List Form} (E : FormulaEquality Γ)
    (hempty : ND.Proof Γ emptyFormula) (hadj : ND.Proof Γ adjunctionFormula)
    (hi : ND.Proof Γ Ordinal.intersectionFormula)
    (hstrict : ND.Proof Γ closedStrictSeparation)
    (hinclusive : ND.Proof Γ closedInclusiveSeparation)
    (hsep : ND.Proof Γ (separationFormula (∼addCoherenceProperty))) :
    ND.Proof Γ (Ordinal.inductionConclusion addCoherenceProperty) :=
  Ordinal.uniformInduction E.core addCoherenceProperty E.transitive hi hadj hsep
    (addCoherenceInductionBase E) (addCoherenceInductionStep E hempty hadj hstrict hinclusive)

#print axioms addCoherenceInductionBase
#print axioms addCoherenceInductionStep
#print axioms additionCoherenceConclusion
end M6.PA.RelationalSource.PairGraph
