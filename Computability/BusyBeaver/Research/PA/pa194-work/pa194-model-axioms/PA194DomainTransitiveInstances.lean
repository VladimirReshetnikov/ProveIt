import PA194DomainTransitiveAtCode
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
namespace PA194DomainTransitiveInstances
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194DomainTransitiveAtCode PA194DomainTransitiveClosedModel PA194DomainTransitiveClosedTemplate PA194DomainInstances PA194FullSepWitnessBranch PA194ContextTripleSpecializeCode PA194TraceMemberForwardCode PA194ContextDoubleSpecializeCode PA194FixedSyntaxQuote PA194OrdinalStepQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

theorem domainS3At (s b m : M) :
    ((⌜domainS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar s] : Formula M SourceL) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s] := by
  have hs : domainS3 = PA194OrdinalBaseQuote.domainTemplate ⇜ ![#2] := by
    simp [domainS3,PA194OrdinalBaseQuote.domainTemplate]
    ordinalSyntax
  have ht : (⌜domainS3⌝ : Semiformula M SourceL 3) =
      (⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.bvar 2] := by
    rw [hs, Semiformula.typed_quote_substs]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [ht]
  simp [Semiformula.substs_substs]

theorem memberBS3At (s b m : M) :
    ((⌜memberBS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar s] : Formula M SourceL) =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s] := by
  simp [memberBS3,ND.mem,Matrix.vecHead,Matrix.vecTail]

theorem memberMB3At (s b m : M) :
    ((⌜memberMB3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar s] : Formula M SourceL) =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b] := by
  simp [memberMB3,ND.mem,Matrix.vecHead,Matrix.vecTail]

theorem memberMS3At (s b m : M) :
    ((⌜memberMS3⌝ : Semiformula M SourceL 3).subst ![Semiterm.fvar m,Semiterm.fvar b,Semiterm.fvar s] : Formula M SourceL) =
      Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar s] := by
  simp [memberMS3,ND.mem,Matrix.vecHead,Matrix.vecTail]

noncomputable def domainTransAlignedProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar s]) : Formula M SourceL) Γ := by
  let hd' := TDerivation.cast (congrArg (fun q => insert q Γ) (domainS3At s b m).symm) hd
  let hs' := TDerivation.cast (congrArg (fun q => insert q Γ) (memberBS3At s b m).symm) hbs
  let hm' := TDerivation.cast (congrArg (fun q => insert q Γ) (memberMB3At s b m).symm) hmb
  let out := domainTransAtProof T Γ s b m du hd' hs' hm'
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (memberMS3At s b m)) out

@[simp] theorem domainTransAlignedProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s b m : M)
    (du : T ⊢!ᵈᵉʳ insert (⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    (domainTransAlignedProof T Γ s b m du hd hbs hmb).val = domainTransAtCode s b m Γ.val du.val hd.val hbs.val hmb.val := by
  simp [domainTransAlignedProof]

noncomputable def domainTransAlignedFromLogic (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (s b m : M)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar s]) Γ)
    (hbs : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar b,Semiterm.fvar s]) : Formula M SourceL) Γ)
    (hmb : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar b]) : Formula M SourceL) Γ) :
    T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.fvar m,Semiterm.fvar s]) : Formula M SourceL) Γ := by
  let uq : Formula M SourceL := ⌜(∀⁰ ∀⁰ ∀⁰ domainTransBound : Proposition M6.PA.RelationalSource.language)⌝
  let du : T ⊢!ᵈᵉʳ insert uq Γ := TDerivation.wk (domainTransUniversalProof T) (by intro x hx; simp at hx ⊢; tauto)
  exact domainTransAlignedProof T Γ s b m du hd hbs hmb

#print axioms domainS3At
#print axioms memberBS3At
#print axioms memberMB3At
#print axioms memberMS3At
#print axioms domainTransAlignedProof
#print axioms domainTransAlignedProof_val
#print axioms domainTransAlignedFromLogic
end models
end PA194DomainTransitiveInstances
