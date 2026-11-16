import PA194SeparationTraceOpen
import PA194ContextExsWitnessCode
import PA194InternalInductionStepShift
import PA194SeparationShiftCode
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Typed
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194TracePropertyCompose
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationTraceWitness PA194SeparationTraceShift PA194ContextExsWitnessCode PA194ContextExsElimCode PA194SeparationTraceAtCode PA194SeparationShiftCode PA194InternalSeparationShift PA194BindSource PA194ContextShiftCode PA194ContextModusPonensCode PA194ContextConjunctionCode PA194ContextSpecializeCode
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

/-- The property leaf follows the opened-witness substitution environment. -/
theorem tracePropertyCompose (P : Semiformula M SourceL 1) (s x : M) :
    (((((P.subst ![Semiterm.bvar 0] : Semiformula M SourceL 3).subst
      (SemitermVec.q (SemitermVec.q ![Semiterm.fvar s]))).shift).subst
      (SemitermVec.q ![Semiterm.fvar 0])).subst ![Semiterm.fvar x] : Formula M SourceL) =
        P.shift.subst ![Semiterm.fvar x] := by
  simp [Semiformula.shift_substs, Semiformula.substs_substs]

open PA194SeparationTraceOpen M6.PA.RelationalSource

noncomputable def typedSepInner (P : Semiformula M SourceL 1) : Semiformula M SourceL 3 :=
  let pc : Semiformula M SourceL 3 := P.subst ![Semiterm.bvar 0]
  let mc : Semiformula M SourceL 3 := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.bvar 1]
  let ms : Semiformula M SourceL 3 := Bootstrapping.Semiformula.rel Relation.mem ![Semiterm.bvar 0,Semiterm.bvar 2]
  (∼mc ⋎ (ms ⋏ pc)) ⋏ ((∼ms ⋎ ∼pc) ⋎ mc)

noncomputable def traceTransform (φ : Semiformula M SourceL 3) (s x : M) : Formula M SourceL :=
  ((φ.subst (SemitermVec.q (SemitermVec.q ![Semiterm.fvar s]))).shift.subst
      (SemitermVec.q ![Semiterm.fvar 0])).subst ![Semiterm.fvar x]

/-- The expanded trace at an arbitrary internal index. -/
theorem traceTyped_expand (P : Semiformula M SourceL 1) (s x : M) :
    traceTransform (typedSepInner P) s x =
      let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]
      let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
      let prop : Formula M SourceL := P.shift.subst ![Semiterm.fvar x]
      (∼mc ⋎ (ms ⋏ prop)) ⋏ ((∼ms ⋎ ∼prop) ⋎ mc) := by
  simp [typedSepInner,traceTransform,Semiformula.shift_substs,Semiformula.substs_substs,SemitermVec.q,Matrix.cons_val]

theorem typedSepInner_val (P : Semiformula M SourceL 1) :
    (typedSepInner P).val = sepInner P.val := by
  have h := congrArg Semiformula.val (Semiformula.subst_eq_self₁ P)
  change subst SourceL (?[ ^#(0 : M)] : M) P.val = P.val at h
  simp [typedSepInner,sepInner,relExtVector,SemitermVec.val_succ, ←adjoin_def,h]
  all_goals change ((1 : Nat) : M) = 1 <;> simp

theorem traceTransform_val (P : Semiformula M SourceL 1) (s x : M) :
    (traceTransform (typedSepInner P) s x).val =
      substs1 SourceL (^&x) (traceOpenBodyCode P.val s) := by
  simp [traceTransform,traceOpenBodyCode,traceInnerCode,typedSepInner_val,
    Bootstrapping.Semiformula.val_substs,Bootstrapping.Semiformula.val_shift,
    SemitermVec.q_val_eq_qVec,SemitermVec.val_succ,substs1,qVec,one_add_one_eq_two]

/-- Exact expanded form of the opened separation trace at x. -/
theorem traceAt_expanded (p s x : M) (hp : IsSemiformula SourceL 1 p) :
    (⟨traceOpenBodyCode p s, by simpa using traceOpenBody_scoped p s hp⟩ : Semiformula M SourceL 1).subst ![Semiterm.fvar x] =
      let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]
      let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
      let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
      let prop : Formula M SourceL := P.shift.subst ![Semiterm.fvar x]
      (∼mc ⋎ (ms ⋏ prop)) ⋏ ((∼ms ⋎ ∼prop) ⋎ mc) := by
  let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
  apply Semiformula.ext
  have h := congrArg Semiformula.val (traceTyped_expand P s x)
  have ht := traceTransform_val P s x
  simp [P,substs1,SemitermVec.val_succ] at ht ⊢
  rw [← ht]
  simpa [P,substs1,SemitermVec.val_succ] using h

/-- Use an opened trace to derive the expanded membership/property equivalence. -/
noncomputable def expandedTraceAtProof (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ) :
    T ⊢!ᵈᵉʳ insert (let mc : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar 0]
      let ms : Formula M SourceL := Semiformula.rel Relation.mem ![Semiterm.fvar x,Semiterm.fvar (s+1)]
      let P : Semiformula M SourceL 1 := ⟨p, by simpa using hp⟩
      let prop : Formula M SourceL := P.shift.subst ![Semiterm.fvar x]
      (∼mc ⋎ (ms ⋏ prop)) ⋏ ((∼ms ⋎ ∼prop) ⋎ mc)) Γ := by
  let out := traceAtProof T Γ p s x hp d
  exact TDerivation.cast (congrArg (fun q => insert q Γ) (traceAt_expanded p s x hp)) out

@[simp] theorem expandedTraceAtProof_val (T : InternalTheory M SourceL) (Γ : Sequent M SourceL)
    (p s x : M) (hp : IsSemiformula SourceL 1 p)
    (d : T ⊢!ᵈᵉʳ insert ((⟨traceBodyCode p s, by simpa using traceBody_scoped p s hp⟩ : Semiformula M SourceL 1).free) Γ) :
    (expandedTraceAtProof T Γ p s x hp d).val = traceAtProofCode p s x Γ.val d.val := by
  simp [expandedTraceAtProof]

#print axioms expandedTraceAtProof
#print axioms expandedTraceAtProof_val
#print axioms traceAt_expanded
#print axioms typedSepInner_val
#print axioms traceTransform_val
#print axioms traceTyped_expand
#print axioms tracePropertyCompose
end models
end PA194TracePropertyCompose
