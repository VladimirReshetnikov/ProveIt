import PA194FiniteDischarge
import PA194FoundationOrdinalInductionNumeric
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
import PA194InternalOrdinalStatement
import PA194BindFormulaInverse
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194QuotedInduction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194FiniteDischarge PA194InternalOrdinalStatement PA194OrdinalFixed
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

open Derivation2
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Ordinal

lemma quoted_negContext (xs : List (Proposition M6.PA.RelationalSource.language)) (q : Proposition M6.PA.RelationalSource.language) :
    (⌜(xs.map Semiformula.neg ++ [q]).toFinset⌝ : Sequent M SourceL) =
      negContext (xs.map (fun x => (⌜x⌝ : Formula M SourceL))) (⌜q⌝ : Formula M SourceL) := by
  induction xs with
  | nil => simp [negContext, Sequent.insert_empty_eq_singleton]
  | cons a xs ih =>
    simpa [negContext, List.foldr_cons, ← Semiformula.neg_eq] using congrArg (insert (∼(⌜a⌝ : Formula M SourceL))) ih

noncomputable def dischargeQuotedDerivation (T : InternalTheory M SourceL)
    (xs : List (Proposition M6.PA.RelationalSource.language)) (q : Proposition M6.PA.RelationalSource.language)
    (d : LO.FirstOrder.Derivation (xs.map Semiformula.neg ++ [q]))
    (h : ∀ p ∈ xs, T ⊢! (⌜p⌝ : Formula M SourceL)) : T ⊢! (⌜q⌝ : Formula M SourceL) := by
  have hd : DerivationOf T.theory (⌜d⌝ : M) (⌜(xs.map Semiformula.neg ++ [q]).toFinset⌝ : M) :=
    LO.FirstOrder.derivation_of_quote_derivation d
  let sd : T ⊢!ᵈᵉʳ (⌜(xs.map Semiformula.neg ++ [q]).toFinset⌝ : Sequent M SourceL) := ⟨⌜d⌝, hd⟩
  have hd' : T ⊢!ᵈᵉʳ negContext (xs.map (fun x => (⌜x⌝ : Formula M SourceL))) (⌜q⌝ : Formula M SourceL) := by
    rw [← quoted_negContext]
    exact sd
  apply dischargeFinite T _ _ hd'
  intro p hp
  let x := Classical.choose (List.mem_map.mp hp)
  have hx := Classical.choose_spec (List.mem_map.mp hp)
  exact hx.2 ▸ h x hx.1

/-- A standard typed property has an internal ordinal-induction proof, provided
all formulas of the existing finite standard context have internal proofs. -/
noncomputable def standardOrdinalProof (T : InternalTheory M SourceL)
    (p : Semiproposition M6.PA.RelationalSource.language 1)
    (h : ∀ q ∈ inductionContext p, T ⊢! (⌜q⌝ : Formula M SourceL)) :
    T ⊢! (⌜inductionStatement p⌝ : Formula M SourceL) :=
  dischargeQuotedDerivation T (inductionContext p) (inductionStatement p)
    (PA194Logic.Relational.Source.Ordinal.inductionFoundationDerivation p) h

#print axioms standardOrdinalProof
#print axioms quoted_negContext
#print axioms dischargeQuotedDerivation
end models
end PA194QuotedInduction
