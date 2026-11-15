import PA194LeastExcludesAtCode
import PA194DomainInstances
import PA194FullSepWitnessBranch
import PA194ContextTripleSpecializeCode
import PA194TraceMemberForwardCode
import PA194ContextDoubleSpecializeCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194LeastExcludesInstances
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194LeastExcludesAtCode PA194DomainInstances PA194FullSepWitnessBranch PA194LeastExcludesClosedModel PA194LeastExcludesClosedTemplate PA194ContextTripleSpecializeCode PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
open M6.PA.RelationalSource M6.PA.RelationalSource.ND M6.PA.RelationalSource.Ordinal

section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance boundSepZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance boundSepOne : One M := ⟨F oneCode Fin.elim0⟩
local instance boundSepAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance boundSepMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance boundSepLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance boundSepIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

open M6.PA.RelationalSource

open M6.PA.RelationalSource

theorem domainB3At (c b m : M) :
    ((⌜domainB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c] : Formula M SourceL) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b] := by
  have hs : domainB3 = PA194OrdinalBaseQuote.domainTemplate ⇜ ![#1] := by
    simp [domainB3,PA194OrdinalBaseQuote.domainTemplate]
    ordinalSyntax
  have ht : (⌜domainB3⌝ : Semiformula M SourceL 3) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 1] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

theorem memberBM3At (c b m : M) :
    ((⌜memberBM3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c] : Formula M SourceL) =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b] := by
  simp [memberBM3,ND.mem,Matrix.vecHead,Matrix.vecTail]

theorem memberCM3At (c b m : M) :
    ((⌜memberCM3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c] : Formula M SourceL) =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar c] := by
  simp [memberCM3,ND.mem,Matrix.vecHead,Matrix.vecTail]

/-- Least exclusion using the standard one-variable domain and membership syntax. -/
noncomputable def leastExcludesAlignedProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert (∼(Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar c] : Formula M SourceL)) Γ := by
  let hd' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainB3At c b m).symm) hd
  let hm' := TDerivation.cast (congrArg (fun q => insert q Γ) (memberBM3At c b m).symm) hm
  let out := leastExcludesAtProof T Γ c b m du hd' hl hm'
  exact TDerivation.cast (congrArg (fun q => insert (∼q) Γ) (memberCM3At c b m)) out

@[simp] theorem leastExcludesAlignedProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ leastExcludesBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : T ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (leastExcludesAlignedProof T Γ c b m du hd hl hm).val = leastExcludesAtCode c b m Γ.val du.val hd.val hl.val hm.val := by
  simp [leastExcludesAlignedProof]

noncomputable def leastExcludesAlignedFromTheory (Γ : Sequent M SourceL) (c b m : M)
    (hd : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar b]) Γ)
    (hl : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((⌜leastCB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar c]) Γ)
    (hm : (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (fullSourceInternal (M := M)) ⊢!ᵈᵉʳ insert (∼(Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar c] : Formula M SourceL)) Γ := by
  let T : InternalTheory M SourceL := fullSourceInternal
  let hd' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainB3At c b m).symm) hd
  let hm' := TDerivation.cast (congrArg (fun q => insert q Γ) (memberBM3At c b m).symm) hm
  let out := leastExcludesAtFromTheory Γ c b m hd' hl hm'
  exact TDerivation.cast (congrArg (fun q => insert (∼q) Γ) (memberCM3At c b m)) out

#print axioms leastExcludesAlignedProof
#print axioms leastExcludesAlignedProof_val
#print axioms leastExcludesAlignedFromTheory
#print axioms domainB3At
#print axioms memberBM3At
#print axioms memberCM3At
end models
end PA194LeastExcludesInstances
