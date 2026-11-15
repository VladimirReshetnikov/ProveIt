import PA194NameVariableReflexive
import PA194ContextSpecializeCode
import PA194ContextModusPonensCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
open PA194ContextSpecializeCode PA194ContextModusPonensCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure PRALanguage.language M] [Structure.Eq PRALanguage.language M] [M↓[PRALanguage.language] ⊧* PRA]
local notation "F" => Structure.func (L := PRALanguage.language) (M := M)
local instance elimZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance elimOne : One M := ⟨F oneCode Fin.elim0⟩
local instance elimAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance elimMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance elimLT : LT M := ⟨fun x y => Structure.rel (L := PRALanguage.language) Language.ORing.Rel.lt ![x,y]⟩
local instance elimIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem genericGuardBody_subst (i : M) : substs1 SourceL (^&i) (guardBody : M) = guard i := by
  have hw : IsSemitermVec SourceL 1 0 (?[ ^&i] : M) := by simp
  have hd : substs1 SourceL (^&i) (domainCode (^#(0 : M))) = domainCode (^&i) := by
    unfold substs1
    rw [domainCode_subst (show IsSemiterm SourceL 1 (^#(0 : M)) by simp) hw,termSubst_bvar]
    simp
  change substs1 SourceL (^&i) (neg SourceL (domainCode (^#(0 : M)))) = neg SourceL (domainCode (^&i))
  rw [substs1_negS domainBody_valid (by simp),hd]

theorem guarded_tr_all_specialize (T : InternalTheory M SourceL) {q : M}
    (hq : IsSemiformula PA194PAeq.language 1 q)
    (h : T ⊢! (⟨tr (^∀ q), tr_valid (IsSemiformula.all.mpr (by simpa using hq))⟩ : Formula M SourceL))
    (i : M) : GDerivable T.theory ({tr (substs1 PA194PAeq.language (^&i) q)} : M) := by
  let body : Semiformula M SourceL 1 := ⟨guardBody ^⋎ trBody q, by simpa using IsSemiformula.or.mpr ⟨guardBody_valid,trBody_valid hq⟩⟩
  let Γ : Sequent M SourceL := ⟨guards (i+1),guards_valid (i+1)⟩
  let dom : Formula M SourceL := ⟨domainCode (^&i),domainCode_valid (by simp)⟩
  let atom : Formula M SourceL := ⟨tr (substs1 PA194PAeq.language (^&i) q),tr_valid (IsSemiformula.substs1 (by simp) hq)⟩
  have hall : (⟨tr (^∀ q),tr_valid (IsSemiformula.all.mpr (by simpa using hq))⟩ : Formula M SourceL) = ∀⁰ body := by
    apply Semiformula.ext
    exact tr_all hq
  let hw : T ⊢!ᵈᵉʳ insert (∀⁰ body) Γ := TDerivation.wk
    (TDerivation.cast (congrArg (fun z => insert z ∅) hall) h) (by intro x hx; simp at hx ⊢; tauto)
  let hs := contextSpecializeProof T Γ body (Semiterm.fvar i) hw
  have hi : body.subst ![Semiterm.fvar i] = dom 🡒 atom := by
    apply Semiformula.ext
    change substs1 SourceL (^&i) (guardBody ^⋎ trBody q) = neg SourceL (domainCode (^&i)) ^⋎ tr (substs1 PA194PAeq.language (^&i) q)
    unfold substs1
    rw [substs_or guardBody_valid.isUFormula (trBody_valid hq).isUFormula]
    change substs1 SourceL (^&i) guardBody ^⋎ substs1 SourceL (^&i) (trBody q) = _
    rw [genericGuardBody_subst,←tr_substs1_fvar hq]
    rfl
  let himp := TDerivation.cast (congrArg (fun z => insert z Γ) hi) hs
  have hg : guard i ∈ Γ.val := mem_guards.mpr ⟨i,by simp,rfl⟩
  let hd : T ⊢!ᵈᵉʳ insert dom Γ := TDerivation.em dom (by simp) (by
    simp only [Sequent.mem_insert_iff]
    right
    change neg SourceL (domainCode (^&i)) ∈ Γ.val
    exact hg)
  let out := contextMPProof T Γ dom atom himp hd
  refine ⟨i+1, ?_⟩
  have hsset : (guards (i+1) ∪ ({atom.val} : M)) = insert atom.val (guards (i+1)) := by rw [insert_eq_union_singleton,union_comm]
  rw [hsset]
  exact out.toDerivable


set_option maxHeartbeats 500000 in
theorem guarded_tr_all_specialize_guarded (T : InternalTheory M SourceL) {q : M}
    (hq : IsSemiformula PA194PAeq.language 1 q)
    (h : GDerivable T.theory ({tr (^∀ q)} : M))
    (i : M) : GDerivable T.theory ({tr (substs1 PA194PAeq.language (^&i) q)} : M) := by
  obtain ⟨n, hn⟩ := h
  let k : M := max n (i+1)
  let body : Semiformula M SourceL 1 := ⟨guardBody ^⋎ trBody q, by simpa using IsSemiformula.or.mpr ⟨guardBody_valid,trBody_valid hq⟩⟩
  let Γ : Sequent M SourceL := ⟨guards k,guards_valid k⟩
  let dom : Formula M SourceL := ⟨domainCode (^&i),domainCode_valid (by simp)⟩
  let atom : Formula M SourceL := ⟨tr (substs1 PA194PAeq.language (^&i) q),tr_valid (IsSemiformula.substs1 (by simp) hq)⟩
  have hall : (⟨tr (^∀ q),tr_valid (IsSemiformula.all.mpr (by simpa using hq))⟩ : Formula M SourceL) = ∀⁰ body := by
    apply Semiformula.ext
    exact tr_all hq
  have hn' : Derivable T.theory (guards n ∪ insert (tr (^∀ q)) (∅ : M)) := by
    rw [← singleton_eq_insert]
    exact hn
  have hl' : Derivable T.theory (insert (tr (^∀ q)) (guards k ∪ (∅ : M))) :=
    GDerivable.lift (n := n) (m := k) (p := tr (^∀ q)) (Δ := (∅ : M)) (le_max_left n (i+1)) hn'
  have hl : Derivable T.theory (insert (tr (^∀ q)) (guards k)) := by simpa using hl'
  let hw0 : T ⊢!ᵈᵉʳ insert (⟨tr (^∀ q),tr_valid (IsSemiformula.all.mpr (by simpa using hq))⟩ : Formula M SourceL) Γ :=
    Derivable.toTDerivation _ hl
  let hw : T ⊢!ᵈᵉʳ insert (∀⁰ body) Γ := TDerivation.cast (congrArg (fun z => insert z Γ) hall) hw0
  let hs := contextSpecializeProof T Γ body (Semiterm.fvar i) hw
  have hi : body.subst ![Semiterm.fvar i] = dom 🡒 atom := by
    apply Semiformula.ext
    change substs1 SourceL (^&i) (guardBody ^⋎ trBody q) = neg SourceL (domainCode (^&i)) ^⋎ tr (substs1 PA194PAeq.language (^&i) q)
    unfold substs1
    rw [substs_or guardBody_valid.isUFormula (trBody_valid hq).isUFormula]
    change substs1 SourceL (^&i) guardBody ^⋎ substs1 SourceL (^&i) (trBody q) = _
    rw [genericGuardBody_subst,←tr_substs1_fvar hq]
    rfl
  let himp := TDerivation.cast (congrArg (fun z => insert z Γ) hi) hs
  have hg : guard i ∈ Γ.val := mem_guards.mpr ⟨i,lt_of_lt_of_le (by simp) (le_max_right n (i+1)),rfl⟩
  let hd : T ⊢!ᵈᵉʳ insert dom Γ := TDerivation.em dom (by simp) (by
    simp only [Sequent.mem_insert_iff]
    right
    change neg SourceL (domainCode (^&i)) ∈ Γ.val
    exact hg)
  let out := contextMPProof T Γ dom atom himp hd
  refine ⟨k, ?_⟩
  have hsset : (guards k ∪ ({atom.val} : M)) = insert atom.val (guards k) := by rw [insert_eq_union_singleton,union_comm]
  rw [hsset]
  exact out.toDerivable

#print axioms guarded_tr_all_specialize_guarded
#print axioms guarded_tr_all_specialize
end models
end PA194GuardedCompiler
