import PA194OrdinalFixed
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194FiniteDischarge
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

/-- A finite list of assumptions represented negatively in a one-sided sequent. -/
noncomputable def negContext (xs : List (Formula M SourceL)) (q : Formula M SourceL) : Sequent M SourceL :=
  xs.foldr (fun p g => insert (∼p) g) (insert q ∅)

noncomputable def dischargeFinite (T : InternalTheory M SourceL) (xs : List (Formula M SourceL))
    (q : Formula M SourceL) (d : T ⊢!ᵈᵉʳ negContext xs q)
    (h : ∀ p ∈ xs, T ⊢! p) : T ⊢! q := by
  induction xs with
  | nil => exact TDerivation.toTProof d
  | cons a xs ih =>
    apply ih
    · have ha : T ⊢! a := h a (by simp)
      have hw : T ⊢!ᵈᵉʳ insert a (negContext xs q) := by
        apply TDerivation.wk ha
        intro p hp
        change p ∈ insert a.val (∅ : M) at hp
        have hpa : p = a.val := by simpa using hp
        subst p
        simp
      apply TDerivation.cut hw
      exact d
    · intro p hp
      exact h p (by simp [hp])

#print axioms dischargeFinite
end models
end PA194FiniteDischarge
