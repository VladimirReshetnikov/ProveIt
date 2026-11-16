import PA194IsoGuardProperty
import PA194ContextAllCode
import PA194IsoGuardAt
import PA194TraceDirectSyntax
import PA194TracePropertyCompose
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194IsoGuardShift
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContextAllCode PA194FixedSyntaxQuote PA194IsoGuardProperty PA194TraceDirectSyntax PA194TracePropertyCompose PA194SeparationTraceOpen PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

open M6.PA.RelationalSource




open PA194IsoGuardAt

theorem isoGuard_shift (c : M) (hc : IsSemiformula SourceL 1 c) :
    (⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).shift =
      (⟨isoGuardProperty (shift SourceL c),by simpa using isoGuardProperty_scoped (shift SourceL c) hc.shift⟩ : Semiformula M SourceL 1) := by
  have hg : IsSemiformula SourceL 2 (⌜isoGuardTemplate⌝ : M) := by simpa using Semiformula.quote_isSemiformula (V := M) isoGuardTemplate
  have hf : shift SourceL (⌜isoGuardTemplate⌝ : M) = ⌜isoGuardTemplate⌝ :=
    PA194InternalInductionBaseShift.typed_quote_shift_fixed isoGuardTemplate (by decide)
  apply Semiformula.ext
  change shift SourceL (isoGuardProperty c) = isoGuardProperty (shift SourceL c)
  unfold isoGuardProperty
  rw [shift_all (IsUFormula.or.mpr ⟨hg.neg.isUFormula,hc.isUFormula⟩),shift_or hg.neg.isUFormula hc.isUFormula,shift_neg hg,hf]

theorem isoGuardAt_shift (c a : M) (hc : IsSemiformula SourceL 1 c) :
    (((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a] : Formula M SourceL)).shift =
      (⟨isoGuardProperty (shift SourceL c),by simpa using isoGuardProperty_scoped (shift SourceL c) hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (a+1)] := by
  rw [Semiformula.shift_substs,isoGuard_shift c hc]
  congr 1
  funext i
  fin_cases i <;> simp

noncomputable def isoGuardShiftCode (c a ctx d : M) : M :=
  contextShiftCode (substs1 SourceL (^&a) (isoGuardProperty c)) ctx d

noncomputable def isoGuardShiftGraph : 𝚺₁.Semisentence 5 := .mkSigma
  “out c a ctx d. ∃ q, !isoGuardPropertyGraph q c ∧ ∃ t, !qqFvarDef t a ∧
    ∃ r, !(substs1Graph SourceL) r t q ∧ !contextShiftGraph out r ctx d”

theorem isoGuardShiftGraph_defined :
    𝚺₁.DefinedFunction (fun w : Fin 4 → M => isoGuardShiftCode (w 0) (w 1) (w 2) (w 3)) isoGuardShiftGraph := by
  haveI := isoGuardPropertyGraph_defined (M := M)
  haveI := contextShiftGraph_defined (M := M)
  exact .mk fun w => by simp [isoGuardShiftGraph,isoGuardShiftCode]

noncomputable def isoGuardShiftProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a : M)
    (hc : IsSemiformula SourceL 1 c)
    (d : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty (shift SourceL c),by simpa using isoGuardProperty_scoped (shift SourceL c) hc.shift⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar (a+1)]) Γ.shift := by
  let r : Formula M SourceL := (⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]
  let ds := contextShiftProof T Γ r d
  exact TDerivation.cast (congrArg (fun z => insert z Γ.shift) (isoGuardAt_shift c a hc)) ds

@[simp] theorem isoGuardShiftProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL) (c a : M)
    (hc : IsSemiformula SourceL 1 c)
    (d : T ⊢!ᵈᵉʳ insert ((⟨isoGuardProperty c,by simpa using isoGuardProperty_scoped c hc⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar a]) Γ) :
    (isoGuardShiftProof T Γ c a hc d).val = isoGuardShiftCode c a Γ.val d.val := by
  simp [isoGuardShiftProof,isoGuardShiftCode,substs1,SemitermVec.val_succ]

#print axioms isoGuardShiftGraph_defined
#print axioms isoGuardShiftProof
#print axioms isoGuardShiftProof_val
#print axioms isoGuard_shift
#print axioms isoGuardAt_shift
end models
end PA194IsoGuardShift
