import PA194TraceMemberForwardCode
import PA194OrdinalBadNotZeroCode
import PA194ContextAndProjectionCode
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace PA194TraceBadNotZeroCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194TraceMemberForwardCode PA194OrdinalBadNotZeroCode PA194InductionBaseShiftCode PA194InternalOrdinalBase PA194OrdinalBaseQuote PA194TracePropertyCompose PA194SeparationTraceOpen PA194ContextAndProjectionCode PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- From a trace of the negated property, a bad witness member is nonzero. -/
noncomputable def traceBadNotZeroCode (p s x g dt dm hb hd : M) : M :=
  let np := neg SourceL p
  let sp := shift SourceL p
  let nsp := shift SourceL np
  let ms := memberFvarCode x (s+1)
  let prop := substs1 SourceL (^&x) nsp
  let pair := traceMemberForwardCode np s x g dt dm
  let bad := contextAndRightCode ms prop g pair
  badNotZeroCode sp x g hb hd bad

noncomputable def traceBadNotZeroGraph : 𝚺₁.Semisentence 9 := .mkSigma
  “out p s x g dt dm hb hd. ∃ np, !(negGraph SourceL) np p ∧ ∃ sp, !(shiftGraph SourceL) sp p ∧
    ∃ nsp, !(shiftGraph SourceL) nsp np ∧ ∃ sn, sn = s + 1 ∧ ∃ ms, !memberFvarGraph ms x sn ∧
    ∃ tx, !qqFvarDef tx x ∧ ∃ prop, !(substs1Graph SourceL) prop tx nsp ∧
    ∃ pair, !traceMemberForwardGraph pair np s x g dt dm ∧ ∃ bad, !contextAndRightGraph bad ms prop g pair ∧
    !badNotZeroGraph out sp x g hb hd bad”

theorem traceBadNotZeroGraph_defined :
    𝚺₁.DefinedFunction (fun v : Fin 8 → M => traceBadNotZeroCode (v 0) (v 1) (v 2) (v 3) (v 4) (v 5) (v 6) (v 7)) traceBadNotZeroGraph := by
  haveI := memberFvarGraph_defined (M := M)
  haveI := traceMemberForwardGraph_defined (M := M)
  haveI := contextAndRightGraph_defined (M := M)
  haveI := badNotZeroGraph_defined (M := M)
  exact .mk fun v => by simp [traceBadNotZeroGraph,traceBadNotZeroCode]

noncomputable def traceBadNotZeroProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ) :
    T ⊢!ᵈᵉʳ insert (∼((⌜zeroTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x])) Γ := by
  let ms : Formula M SourceL := Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  let N : Semiformula M SourceL 1 := ⟨neg SourceL p, by simpa using hp.neg⟩
  let ni : Formula M SourceL := N.shift.subst ![Semiterm.fvar x]
  let pi : Formula M SourceL := P.shift.subst ![Semiterm.fvar x]
  let pair := traceMemberForwardProof T Γ (neg SourceL p) s x hp.neg dt dm
  let bad := contextAndRightProof T Γ ms ni pair
  have he : ni = ∼pi := by
    change N.shift.subst ![Semiterm.fvar x] = ∼(P.shift.subst ![Semiterm.fvar x])
    have hN : N = ∼P := by apply Semiformula.ext; rfl
    rw [hN]
    simp
  let bad' := TDerivation.cast (congrArg (fun q => insert q Γ) he) bad
  exact badNotZeroProof T Γ (shift SourceL p) x hp.shift hb hd bad'

@[simp] theorem traceBadNotZeroProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (dt : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode (neg SourceL p) s, by simpa using traceBody_scoped _ s hp.neg⟩ : Semiformula M SourceL 1).free) Γ)
    (dm : T ⊢!ᵈᵉʳ insert ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]) : Formula M SourceL) Γ)
    (hb : T ⊢!ᵈᵉʳ insert (⟨baseCode (shift SourceL p), inductionBaseCode_scoped _ _ _ (Semiformula.quote_isSemiformul₁ _)
      (Semiformula.quote_isSemiformul₁ _) hp.shift⟩ : Formula M SourceL) Γ)
    (hd : T ⊢!ᵈᵉʳ insert ((⌜PA194OrdinalBaseQuote.domainTemplate⌝ : Semiformula M SourceL 1).subst ![Semiterm.fvar x]) Γ) :
    (traceBadNotZeroProof T Γ p s x hp dt dm hb hd).val = traceBadNotZeroCode p s x Γ.val dt.val dm.val hb.val hd.val := by
  have hms : ((Bootstrapping.Semiformula.rel M6.PA.RelationalSource.Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)] : Formula M SourceL)).val = memberFvarCode x (s+1) := by
    simp [memberFvarCode,SemitermVec.val_succ]
    change ((1 : Nat) : M) = 1
    simp
  simp only [traceBadNotZeroProof,traceBadNotZeroCode,badNotZeroProof_val,TDerivation.cast_val,
    contextAndRightProof_val,traceMemberForwardProof_val,Bootstrapping.Semiformula.val_substs,
    Bootstrapping.Semiformula.val_shift,SemitermVec.val_succ,Bootstrapping.Semiterm.fvar_val,hms,substs1]
  simp [Matrix.vecHead,Matrix.vecTail]

#print axioms traceBadNotZeroGraph_defined
#print axioms traceBadNotZeroProof
#print axioms traceBadNotZeroProof_val
end models
end PA194TraceBadNotZeroCode
