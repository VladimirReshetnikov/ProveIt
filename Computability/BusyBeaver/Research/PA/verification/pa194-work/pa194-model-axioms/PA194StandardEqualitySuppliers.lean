import PA194StandardOrdinalReduction
import PA194OrdinalSuppliers
import PA194FoundationOrdinalInductionNumeric
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194StandardEqualitySuppliers
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194StandardOrdinalReduction PA194QuotedInduction PA194OrdinalSuppliers PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
open PA194OrdinalStatementFromProperty PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
  PA194InternalOrdinalBase PA194InternalOrdinalConclusion PA194OrdinalPropertyPlacement PA194OrdinalStepQuote
  PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance freeBoundClosedLeafZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance freeBoundClosedLeafOne : One M := ⟨F oneCode Fin.elim0⟩
local instance freeBoundClosedLeafAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance freeBoundClosedLeafMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance freeBoundClosedLeafLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance freeBoundClosedLeafIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal M6.PA.RelationalSource.PairGraph

open PA194ModelLogic
open M6.PA.RelationalSource
theorem refl_syntax : (sourceEqRefl : Proposition M6.PA.RelationalSource.language) = reflexivityFormula := by
  change Semiformula.rewAux Rew.emb ((∀⁰ (.rel Relation.eq ![#0,#0])) : Sentence M6.PA.RelationalSource.language) = _
  simp [reflexivityFormula,eqAtom,Semiformula.rewAux,Function.comp_def]
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1)
theorem symm_syntax : (sourceEqSymm : Proposition M6.PA.RelationalSource.language) = symmetryFormula := by
  change Semiformula.rewAux Rew.emb ((∀⁰ ∀⁰ (.nrel Relation.eq ![#1,#0] ⋎ .rel Relation.eq ![#0,#1])) : Sentence M6.PA.RelationalSource.language) = _
  simp [symmetryFormula,eqAtom,notEqAtom,Semiformula.rewAux,Function.comp_def]
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1)
theorem trans_syntax : (sourceEqTrans : Proposition M6.PA.RelationalSource.language) = transitivityFormula := by
  change Semiformula.rewAux Rew.emb ((∀⁰ ∀⁰ ∀⁰ (.nrel Relation.eq ![#2,#1] ⋎ (.nrel Relation.eq ![#1,#0] ⋎ .rel Relation.eq ![#2,#0]))) : Sentence M6.PA.RelationalSource.language) = _
  simp [transitivityFormula,eqAtom,notEqAtom,Semiformula.rewAux,Function.comp_def]
  repeat' first
    | rfl
    | (funext i; exact Fin.cases rfl (fun j => Fin.cases rfl (fun k => Fin.elim0 k) j) i)
    | (change Semiformula.and _ _ = Semiformula.and _ _; congr 1)
    | (change Semiformula.or _ _ = Semiformula.or _ _; congr 1)
    | (change Semiformula.all _ = Semiformula.all _; congr 1)
    | (change Semiformula.rel _ _ = Semiformula.rel _ _; congr 1)
    | (change Semiformula.nrel _ _ = Semiformula.nrel _ _; congr 1)

noncomputable def standardAxiomProof (σ : Sentence M6.PA.RelationalSource.language)
    (hσ : σ ∈ adjunctiveFullSepTheory) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜(σ : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) := by
  letI := adjunctiveFullSepTheoryDelta
  let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
  apply TProof.byAxm
  change (⌜(σ : Proposition M6.PA.RelationalSource.language)⌝ : M) ∈ adjunctiveFullSepTheory.Δ₁Class
  rw [← Sentence.quote_def]
  exact Δ₁Class.mem_iff.mpr hσ

noncomputable def reflexivityProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜reflexivityFormula⌝ : Formula M SourceL) := by
  have hσ : sourceEqRefl ∈ adjunctiveFullSepTheory := by
    change sourceEqRefl ∈ adjunctiveTheory ∪ fullSepTheory
    left
    simp [adjunctiveTheory, adjunctiveList]
  have h := standardAxiomProof (M := M) sourceEqRefl hσ
  rw [refl_syntax] at h
  exact h

noncomputable def symmetryProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜symmetryFormula⌝ : Formula M SourceL) := by
  have hσ : sourceEqSymm ∈ adjunctiveFullSepTheory := by
    change sourceEqSymm ∈ adjunctiveTheory ∪ fullSepTheory
    left
    simp [adjunctiveTheory, adjunctiveList]
  have h := standardAxiomProof (M := M) sourceEqSymm hσ
  rw [symm_syntax] at h
  exact h

noncomputable def transitivityProof :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜transitivityFormula⌝ : Formula M SourceL) := by
  have hσ : sourceEqTrans ∈ adjunctiveFullSepTheory := by
    change sourceEqTrans ∈ adjunctiveTheory ∪ fullSepTheory
    left
    simp [adjunctiveTheory, adjunctiveList]
  have h := standardAxiomProof (M := M) sourceEqTrans hσ
  rw [trans_syntax] at h
  exact h

/-- Reduce the standard ordinal proof to three fixed non-axiom premises. -/
noncomputable def standardOrdinalProofOfThree
    (p : Semiproposition M6.PA.RelationalSource.language 1)
    (emptyProof : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜emptyFormula⌝ : Formula M SourceL))
    (adjunctionProof : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜adjunctionFormula⌝ : Formula M SourceL))
    (congruenceProof : let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
      T ⊢! (⌜congruenceFormula⌝ : Formula M SourceL)) :
    let T : InternalTheory M SourceL := ⟨adjunctiveFullSepTheory, adjunctiveFullSepTheoryDelta⟩
    T ⊢! (⌜inductionStatement p⌝ : Formula M SourceL) := by
  apply standardOrdinalProofOfExactContext p
  dsimp only
  intro q hq
  by_cases h0 : q = emptyFormula
  · subst q; exact emptyProof
  by_cases h1 : q = adjunctionFormula
  · subst q; exact adjunctionProof
  by_cases h2 : q = reflexivityFormula
  · subst q; exact reflexivityProof
  by_cases h3 : q = symmetryFormula
  · subst q; exact symmetryProof
  by_cases h4 : q = transitivityFormula
  · subst q; exact transitivityProof
  have h5 : q = congruenceFormula := by
    simpa [exactContext, h0, h1, h2, h3, h4] using hq
  subst q
  exact congruenceProof

#print axioms standardOrdinalProofOfThree
#print axioms reflexivityProof
#print axioms symmetryProof
#print axioms transitivityProof
end models
end PA194StandardEqualitySuppliers
