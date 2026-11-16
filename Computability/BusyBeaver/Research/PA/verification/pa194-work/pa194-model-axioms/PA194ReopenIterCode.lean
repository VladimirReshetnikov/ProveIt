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
namespace PA194ReopenIterCode
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

open PA194ReopenOneCode PA194ContextSpecializeCode PA194ContextShiftCode PA194FixedSyntaxQuote PA194OrdinalFixed


/-- A model-length iteration of the explicit one-step reopening code. -/
noncomputable def reopenIterBlueprint : PR.Blueprint 3 where
  zero := .mkSigma “out p n d. out = d”
  succ := .mkSigma “out previous index p n d.
    ∃ k, !subDef k n (index+1) ∧ ∃ closed, !closeIterBlueprint.resultDef closed k p ∧ !reopenOneGraph out closed previous”

noncomputable def reopenIterConstruction : PR.Construction M reopenIterBlueprint where
  zero := fun v => v 2
  succ := fun v i previous => reopenOneCode (modelClose (v 1 - (i+1)) (v 0)) previous
  zero_defined := .mk fun v => by simp [reopenIterBlueprint]
  succ_defined := .mk fun v => by
    haveI := reopenOneGraph_defined (M := M)
    have hv : (fun _ : Fin 1 => v 3) = ![v 3] := by funext i; fin_cases i; rfl
    simp [reopenIterBlueprint,modelClose,closeIterConstruction.result_defined_iff,hv]

noncomputable def reopenIterCode (p n d i : M) : M :=
  (reopenIterConstruction (M := M)).result ![p,n,d] i

@[simp] theorem reopenIterCode_zero (p n d : M) : reopenIterCode p n d 0 = d := by
  simp [reopenIterCode,reopenIterConstruction]

theorem reopenIterCode_succ (p n d i : M) :
    reopenIterCode p n d (i+1) = reopenOneCode (modelClose (n-(i+1)) p) (reopenIterCode p n d i) := by
  simp [reopenIterCode,reopenIterConstruction]

noncomputable def reopenIterGraph : 𝚺₁.Semisentence 5 :=
  reopenIterBlueprint.resultDef |>.rew (Rew.subst ![#0,#4,#1,#2,#3])

theorem reopenIterGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 4 → M => reopenIterCode (v 0) (v 1) (v 2) (v 3)) reopenIterGraph := .mk fun v => by
  simp [(reopenIterConstruction (M := M)).result_defined_iff,reopenIterGraph]
  rfl

/-- Every internal step reopens one closure, including nonstandard lengths. -/
theorem reopenIter_derivation (T : InternalTheory M SourceL) (p n : M)
    (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨modelClose n p, modelClose_scope n p hp⟩ : Formula M SourceL)) :
    ∀ i : M, i ≤ n → DerivationOf T.theory (reopenIterCode p n d.val i) ({modelClose (n-i) p} : M) := by
  haveI : 𝚺₁-Function₂ (modelClose : M → M → M) := modelClose_definable
  have hiter : 𝚺₁-Function₁ (fun i : M => reopenIterCode p n d.val i) := by
    have hf : 𝚺₁.DefinableFunction (fun v : Fin 4 → M => reopenIterCode (v 0) (v 1) (v 2) (v 3)) :=
      (reopenIterGraph_defined (M := M)).to_definable
    have h := HierarchySymbol.DefinableFunction.substitution (Γ := 𝚺) (m := 0)
      (f := ![fun _ : Fin 1 → M => p, fun _ => n, fun _ => d.val, fun v => v 0]) hf
      (by simp [Fin.forall_fin_iff_zero_and_forall_succ])
    simpa using h
  haveI := hiter
  have hdef : 𝚺₁-Predicate (fun i : M => i ≤ n → DerivationOf T.theory (reopenIterCode p n d.val i) ({modelClose (n-i) p} : M)) := by
    definability
  intro i
  induction i using ISigma1.sigma1_succ_induction with
  | hP => exact hdef
  | zero =>
    intro hle
    simpa [reopenIterCode_zero] using d.derivationOf
  | succ i ih =>
    intro hle
    have hil : i ≤ n := le_trans (by simp) hle
    have hlt : i < n := lt_of_lt_of_le (lt_add_one i) hle
    have old := ih hil
    have heq : n - (i+1) + 1 = n-i := by simpa using sub_succ_add_succ hlt (0 : M)
    have hc : closeOne (modelClose (n-(i+1)) p) = modelClose (n-i) p := by
      rw [← heq, modelClose_succ]
    let q := modelClose (n-(i+1)) p
    have hq : IsSemiformula SourceL 0 q := modelClose_scope _ p hp
    have old' : DerivationOf T.theory (reopenIterCode p n d.val i) ({closeOne q} : M) := by
      simpa [q,hc] using old
    let pd : T ⊢! (⟨closeOne q,closeOne_scoped q hq⟩ : Formula M SourceL) :=
      ⟨reopenIterCode p n d.val i, by simpa using old'⟩
    have next := (reopenOneProof T q hq pd).derivationOf
    rw [reopenIterCode_succ]
    simpa [q] using next

noncomputable def reopenIterProof (T : InternalTheory M SourceL) (p n : M)
    (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨modelClose n p, modelClose_scope n p hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨p,hp⟩ : Formula M SourceL) := by
  have h := reopenIter_derivation T p n hp d n (le_refl n)
  refine ⟨reopenIterCode p n d.val n, ?_⟩
  simpa [modelClose_zero] using h

@[simp] theorem reopenIterProof_val (T : InternalTheory M SourceL) (p n : M)
    (hp : IsSemiformula SourceL 0 p)
    (d : T ⊢! (⟨modelClose n p, modelClose_scope n p hp⟩ : Formula M SourceL)) :
    (reopenIterProof T p n hp d).val = reopenIterCode p n d.val n := rfl

#print axioms reopenIter_derivation
#print axioms reopenIterProof
#print axioms reopenIterProof_val
#print axioms reopenIterCode_zero
#print axioms reopenIterCode_succ
#print axioms reopenIterGraph_defined
end models
end PA194ReopenIterCode
