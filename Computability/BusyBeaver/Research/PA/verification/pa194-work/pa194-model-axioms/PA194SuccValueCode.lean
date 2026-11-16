import PA194SuccValueInstance
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194SuccValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def succTotalCode : V := ^∀ (neg SourceL (domainCode (^#(0 : V))) ^⋎
  ^∃ (domainCode (^#(0 : V)) ^⋏ successorCode (^#(1 : V)) (^#(0 : V))))

theorem instance_code (s r : V) (hs : IsSemiterm PA194PAeq.language 0 s)
    (hr : IsSemiformula SourceL 1 r)
    (heq : valBody s = domainCode (^#(0 : V)) ^⋏ r) :
    (instS (σ r hr) schema).val = neg SourceL succTotalCode ^⋎
      (neg SourceL (^∃ (valBody s)) ^⋎ (^∃ (valBody (succT s)))) := by
  rw [valBody_succ hs,heq]
  simp only [schema,succTotal,hasValue,succValue,instS_imp,instS_exs,instS_all,instS_and,dom,rest,rel,instS_rel]
  dsimp [ar,L]
  simp only [tqS_vec1,tqS_vec2,tqS_bvar]
  have hσ0 : (σ r hr 0).val = domainCode (^#(0 : V)) := by rfl
  have hσ1 : (σ r hr 1).val = r := by rfl
  have hσ2 : (σ r hr 2).val = successorCode (^#(0 : V)) (^#(1 : V)) := by rfl
  simp only [hσ0,hσ1,hσ2,SemitermVec.val,Matrix.vecHead,Matrix.vecTail]
  simp [matrixToVec_succ,matrixToVec_nil,Matrix.vecHead,Matrix.vecTail]
  have h0 : IsSemiterm SourceL 1 (^#(0 : V)) := by simp
  have h1 : IsSemiterm SourceL 2 (^#(1 : V)) := by simp
  have h2 : IsSemiterm SourceL 2 (^#(0 : V)) := by simp
  have hw1 : IsSemitermVec SourceL 1 1 (?[^#(0 : V)] : V) := by simp
  have hw2 : IsSemitermVec SourceL 2 2 (?[^#(1 : V),^#(0 : V)] : V) := by simp
  have hd : subst SourceL (?[^#(0 : V)] : V) (domainCode (^#(0 : V))) = domainCode (^#(0 : V)) := by
    rw [domainCode_subst h0 hw1]
    simp
  have ht : subst SourceL (?[^#(1 : V),^#(0 : V)] : V) (successorCode (^#(0 : V)) (^#(1 : V))) =
      successorCode (^#(1 : V)) (^#(0 : V)) := by
    rw [successorCode_subst h2 h1 hw2]
    simp
  have hwid : IsSemitermVec SourceL 2 2 (?[^#(0 : V),^#(1 : V)] : V) := by simp
  have htid : subst SourceL (?[^#(0 : V),^#(1 : V)] : V) (successorCode (^#(0 : V)) (^#(1 : V))) =
      successorCode (^#(0 : V)) (^#(1 : V)) := by
    rw [successorCode_subst h2 h1 hwid]
    simp
  have hid : subst SourceL (?[^#(0 : V)] : V) r = r := by
    exact subst_eq_self hr (by simp) (fun i hi => by
      have h : i = 0 := by simpa using hi
      subst i
      simp)
  have ha : IsSemiformula SourceL 1 (domainCode (^#(0 : V)) ^⋏ r) :=
    IsSemiformula.and.mpr ⟨domainCode_valid h0,hr⟩
  have hidAll : subst SourceL (?[^#(0 : V)] : V) (domainCode (^#(0 : V)) ^⋏ r) =
      domainCode (^#(0 : V)) ^⋏ r := by
    exact subst_eq_self ha (by simp) (fun i hi => by
      have h : i = 0 := by simpa using hi
      subst i
      simp)
  rw [hd,ht,hid]
  simp only [succTotalCode,successorValue,substs1,hidAll,termBShift_bvar,imp,htid,zero_add]
#print axioms instance_code
end generic
end PA194SuccValueSchema
