import PA194CloseOneCode
import PA194ReopenOneCode
import PA194ContextSpecializeCode
import PA194ContextShiftCode
import PA194OrdinalClosed
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
import PA194OrdinalStatementFromProperty
import PA194OrdinalBaseQuote
import PA194OrdinalConclusionQuote
import PA194OrdinalStatementQuote
import PA194FoundationOrdinalInductionSchema
import PA194TypedSepQuote
import PA194SourceSeparation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194CloseIterCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open M6.PA.RelationalSource
open PA194OrdinalStatementFromProperty PA194OrdinalStepFromProperty PA194OrdinalBaseQuote PA194OrdinalConclusionQuote
  PA194InternalOrdinalBase PA194InternalOrdinalConclusion PA194InternalOrdinalStatement PA194OrdinalStatementQuote
open PA194OrdinalPropertyPlacement PA194OrdinalStepQuote PA194TypedSeparation PA194InternalOrdinalStep M6.PA.RelationalSource.Ordinal
open PA194BindSource
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance ordinalFixedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance ordinalFixedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance ordinalFixedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance ordinalFixedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance ordinalFixedLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance ordinalFixedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open PA194CloseOneCode PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


/-- Iterate explicit closure proofs over arbitrary model lengths. -/
noncomputable def closeProofIterBlueprint : PR.Blueprint 2 where
  zero := .mkSigma “out p d. out = d”
  succ := .mkSigma “out previous index p d.
    ∃ closed, !closeIterBlueprint.resultDef closed index p ∧ !closeOneGraph out closed previous”

noncomputable def closeProofIterConstruction : PR.Construction M closeProofIterBlueprint where
  zero := fun v => v 1
  succ := fun v i previous => closeOneCode (modelClose i (v 0)) previous
  zero_defined := .mk fun v => by simp [closeProofIterBlueprint]
  succ_defined := .mk fun v => by
    haveI := closeOneGraph_defined (M := M)
    have hv : (fun _ : Fin 1 => v 3) = ![v 3] := by funext i; fin_cases i; rfl
    simp [closeProofIterBlueprint,modelClose,closeIterConstruction.result_defined_iff,hv]

noncomputable def closeProofIterCode (p d i : M) : M :=
  (closeProofIterConstruction (M := M)).result ![p,d] i

@[simp] theorem closeProofIterCode_zero (p d : M) : closeProofIterCode p d 0 = d := by
  simp [closeProofIterCode,closeProofIterConstruction]

theorem closeProofIterCode_succ (p d i : M) :
    closeProofIterCode p d (i+1) = closeOneCode (modelClose i p) (closeProofIterCode p d i) := by
  simp [closeProofIterCode,closeProofIterConstruction]

noncomputable def closeProofIterGraph : 𝚺₁.Semisentence 4 :=
  closeProofIterBlueprint.resultDef |>.rew (Rew.subst ![#0,#3,#1,#2])

theorem closeProofIterGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 3 → M => closeProofIterCode (v 0) (v 1) (v 2)) closeProofIterGraph := .mk fun v => by
  simp [(closeProofIterConstruction (M := M)).result_defined_iff,closeProofIterGraph]
  rfl

theorem closeProofIter_derivation (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 0 p) (d : T ⊢! (⟨p,hp⟩ : Formula M SourceL)) :
    ∀ i : M, DerivationOf T.theory (closeProofIterCode p d.val i) ({modelClose i p} : M) := by
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  have hiter : 𝚺₁-Function₁ (fun i : M => closeProofIterCode p d.val i) := by
    have hf : 𝚺₁.DefinableFunction (fun v : Fin 3 → M => closeProofIterCode (v 0) (v 1) (v 2)) :=
      (closeProofIterGraph_defined (M := M)).to_definable
    have h := HierarchySymbol.DefinableFunction.substitution (Γ := 𝚺) (m := 0)
      (f := ![fun _ : Fin 1 → M => p, fun _ => d.val, fun v => v 0]) hf
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ])
    simpa using h
  haveI := hiter
  have hdef : 𝚺₁-Predicate (fun i : M => DerivationOf T.theory (closeProofIterCode p d.val i) ({modelClose i p} : M)) := by
    definability
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero => simpa [closeProofIterCode_zero,modelClose_zero] using d.derivationOf
  | succ i ih =>
    let q := modelClose i p
    have hq : IsSemiformula SourceL 0 q := modelClose_scope i p hp
    let pd : T ⊢! (⟨q,hq⟩ : Formula M SourceL) :=
      ⟨closeProofIterCode p d.val i, by simpa [q] using ih⟩
    have next := (closeOneCodeProof T q hq pd).derivationOf
    rw [closeProofIterCode_succ,modelClose_succ]
    simpa [q] using next

noncomputable def closeProofIterProof (T : InternalTheory M SourceL) (p n : M)
    (hp : IsSemiformula SourceL 0 p) (d : T ⊢! (⟨p,hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨modelClose n p,modelClose_scope n p hp⟩ : Formula M SourceL) := by
  refine ⟨closeProofIterCode p d.val n, ?_⟩
  simpa using closeProofIter_derivation T p hp d n

@[simp] theorem closeProofIterProof_val (T : InternalTheory M SourceL) (p n : M)
    (hp : IsSemiformula SourceL 0 p) (d : T ⊢! (⟨p,hp⟩ : Formula M SourceL)) :
    (closeProofIterProof T p n hp d).val = closeProofIterCode p d.val n := rfl

#print axioms closeProofIterGraph_defined
#print axioms closeProofIterCode_zero
#print axioms closeProofIterCode_succ
#print axioms closeProofIter_derivation
#print axioms closeProofIterProof
#print axioms closeProofIterProof_val
end models
end PA194CloseIterCode
