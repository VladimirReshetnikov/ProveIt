import PA194InternalSeparationShift
import PA194ModelSepRootGraph
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194SeparationShiftCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BindSource PA194InternalSeparationShift
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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

theorem sepRootPure_model_local (p : M) : sepRootPure p = sepRoot p := by
  simp [sepRootPure,sepRoot,sepInner,relExtVector,adjoin_def]

noncomputable def shiftSeparationCode (p d : M) : M :=
  shiftRule ({sepRoot (shift SourceL p)} : M) d

noncomputable def shiftSeparationCodeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p d. ∃ t, !(shiftGraph SourceL) t p ∧ ∃ r, !sepRootGraph r t ∧
    ∃ s, !expDef s r ∧ !shiftRuleGraph out s d”

theorem shiftSeparationCodeGraph_defined :
    𝚺₁-Function₂ (shiftSeparationCode : M → M → M) via shiftSeparationCodeGraph := by
  haveI := sepRootGraph_defined (V := M)
  refine .mk fun v => ?_
  simp [shiftSeparationCodeGraph, shiftSeparationCode, sepRootPure_model_local, singleton_def]

/-- An explicit proof code for the shifted separation instance. -/
noncomputable def shiftSeparationProofDirect (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL)) :
    T ⊢! (⟨sepRoot (shift SourceL p), sepRoot_scoped (shift SourceL p) hp.shift⟩ : Formula M SourceL) := by
  have he : setShift SourceL ({sepRoot p} : M) = ({sepRoot (shift SourceL p)} : M) := by
    apply mem_ext
    intro x
    simp [mem_setShift_iff, shift_sepRoot p hp]
  have dd : DerivationOf T.theory d.val ({sepRoot p} : M) := by
    simpa [← singleton_eq_insert] using d.derivationOf
  have hd : Derivation T.theory (shiftRule (setShift SourceL ({sepRoot p} : M)) d.val) :=
    Derivation.shiftRule dd
  refine ⟨shiftSeparationCode p d.val, ?_⟩
  constructor
  · simp [shiftSeparationCode]
  · simpa [shiftSeparationCode, he] using hd

@[simp] theorem shiftSeparationProofDirect_val (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨sepRoot p, sepRoot_scoped p hp⟩ : Formula M SourceL)) :
    (shiftSeparationProofDirect T p hp d).val = shiftSeparationCode p d.val := rfl

noncomputable def shiftNegSeparationCode (p d : M) : M :=
  shiftSeparationCode (neg SourceL p) d

noncomputable def shiftNegSeparationCodeGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “out p d. ∃ n, !(negGraph SourceL) n p ∧ !shiftSeparationCodeGraph out n d”

theorem shiftNegSeparationCodeGraph_defined :
    𝚺₁-Function₂ (shiftNegSeparationCode : M → M → M) via shiftNegSeparationCodeGraph := by
  haveI := shiftSeparationCodeGraph_defined (M := M)
  refine .mk fun v => ?_
  simp [shiftNegSeparationCodeGraph, shiftNegSeparationCode]

noncomputable def shiftNegSeparationProofDirect (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL)) :
    T ⊢! (⟨sepRoot (neg SourceL (shift SourceL p)), sepRoot_scoped _ hp.shift.neg⟩ : Formula M SourceL) := by
  let h := shiftSeparationProofDirect T (neg SourceL p) hp.neg d
  refine ⟨shiftNegSeparationCode p d.val, ?_⟩
  have hd := h.derivationOf
  change DerivationOf T.theory (shiftNegSeparationCode p d.val)
    (insert (sepRoot (shift SourceL (neg SourceL p))) (∅ : M)) at hd
  change DerivationOf T.theory (shiftNegSeparationCode p d.val)
    (insert (sepRoot (neg SourceL (shift SourceL p))) (∅ : M))
  rw [shift_neg hp] at hd
  exact hd

@[simp] theorem shiftNegSeparationProofDirect_val (T : InternalTheory M SourceL) (p : M)
    (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢! (⟨sepRoot (neg SourceL p), sepRoot_scoped _ hp.neg⟩ : Formula M SourceL)) :
    (shiftNegSeparationProofDirect T p hp d).val = shiftNegSeparationCode p d.val := rfl

#print axioms shiftNegSeparationCodeGraph_defined
#print axioms shiftNegSeparationProofDirect
#print axioms shiftNegSeparationProofDirect_val
#print axioms shiftSeparationCodeGraph_defined
#print axioms shiftSeparationProofDirect
#print axioms shiftSeparationProofDirect_val
end models
end PA194SeparationShiftCode
