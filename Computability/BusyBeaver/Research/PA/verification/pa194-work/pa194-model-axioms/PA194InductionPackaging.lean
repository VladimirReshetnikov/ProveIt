import PA194OrdinalFixed
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InductionPackaging
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalOrdinalStatement PA194OrdinalFixed
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

/-- Package a one-sided derivation of base, step ⊢ conclusion into the
internal proof of the ordinal-induction implication. -/
noncomputable def packageInductionProof (T : InternalTheory M SourceL)
    (base step conclusion : Formula M SourceL)
    (d : T ⊢!ᵈᵉʳ insert (∼step) (insert conclusion (insert (∼base) ∅))) :
    T ⊢! (base 🡒 (step 🡒 conclusion)) := by
  have h : T ⊢!ᵈᵉʳ insert ((∼step) ⋎ conclusion) (insert (∼base) ∅) := TDerivation.or d
  have h' : T ⊢!ᵈᵉʳ insert (∼base) (insert ((∼step) ⋎ conclusion) ∅) := by
    convert h using 1
    ext x
    simp [or_comm]
  apply TDerivation.toTProof
  simpa [Semiformula.imp_def] using TDerivation.or h'

theorem package_induction_derivable (T : InternalTheory M SourceL) (b s c : M)
    (hb : IsSemiformula SourceL 0 b) (hs : IsSemiformula SourceL 0 s)
    (hc : IsSemiformula SourceL 0 c)
    (hd : Derivable T.theory (insert (neg SourceL s) (insert c (insert (neg SourceL b) (∅ : M))))) :
    Provable T.theory (inductionStatementCode b s c) := by
  let base : Formula M SourceL := ⟨b, hb⟩
  let step : Formula M SourceL := ⟨s, hs⟩
  let conclusion : Formula M SourceL := ⟨c, hc⟩
  have h : T ⊢!ᵈᵉʳ insert (∼step) (insert conclusion (insert (∼base) ∅)) :=
    Derivable.toTDerivation _ (by simpa [base, step, conclusion] using hd)
  have hp : T ⊢ (base 🡒 (step 🡒 conclusion)) := ⟨packageInductionProof T base step conclusion h⟩
  have hv := TProvable.iff_provable.mp hp
  simpa [inductionStatementCode, Semiformula.imp_def, base, step, conclusion] using hv

/-- The remaining internal ordinal obligation is the one-sided base/step sequent. -/
theorem ordinal_code_of_induction_sequent (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (hd : Derivable T.theory
      (insert (neg SourceL (ordinalStepFromProperty (⌜domainOne⌝ : M) (⌜domainZero⌝ : M)
          (⌜successorTemplate⌝ : M) p))
        (insert (inductionConclusionCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M) p)
          (insert (neg SourceL (inductionBaseCode (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : M)
            (⌜zeroTemplate⌝ : M) p)) (∅ : M))))) :
    Provable T.theory (ordinalInductionCode p) := by
  apply package_induction_derivable T _ _ _ ?_ ?_ ?_ hd
  · exact inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _) (Semiformula.quote_isSemiformul₁ _) hp
  · apply ordinalStepFromProperty_scoped
    · simpa using (Semiformula.quote_isSemiformula domainOne : IsSemiformula SourceL ((2 : Nat) : M) _)
    · simpa using (Semiformula.quote_isSemiformula domainZero : IsSemiformula SourceL ((2 : Nat) : M) _)
    · simpa using (Semiformula.quote_isSemiformula successorTemplate : IsSemiformula SourceL ((2 : Nat) : M) _)
    · exact hp
  · exact inductionConclusionCode_scoped _ _ (Semiformula.quote_isSemiformul₁ _) hp

#print axioms ordinal_code_of_induction_sequent
#print axioms packageInductionProof
#print axioms package_induction_derivable
end models
end PA194InductionPackaging
