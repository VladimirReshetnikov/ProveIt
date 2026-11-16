import PA194NameValueInstance
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194NameValueSchema
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194Schematic PA194GuardedCompiler PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem instance_code (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    (instS (σ s hs) schema).val = neg SourceL (tr (exName s)) ^⋎ (^∃ (valBody s)) := by
  rw [tr_exName hs]
  simp only [schema,instS_imp,instS_exs,instS_and,dom,var,val,iso,instS_rel]
  dsimp [ar,L]
  simp only [tqS_vec1,tqS_vec2,tqS_bvar]
  have hσ0 : (σ s hs 0).val = domainCode (^#(0 : V)) := by rfl
  have hσ1 : (σ s hs 1).val = variableValue (^#(0 : V)) (^#(1 : V)) := by rfl
  have hσ2 : (σ s hs 2).val = valBody s := by rfl
  have hσ3 : (σ s hs 3).val = orderIsoCode (^#(0 : V)) (^#(1 : V)) := by rfl
  simp only [hσ0,hσ1,hσ2,hσ3,SemitermVec.val,Matrix.vecHead,Matrix.vecTail]
  simp [matrixToVec_succ,matrixToVec_nil,Matrix.vecHead,Matrix.vecTail]
  have h0 : IsSemiterm SourceL 1 (^#(0 : V)) := by simp
  have h1 : IsSemiterm SourceL 2 (^#(1 : V)) := by simp
  have h2 : IsSemiterm SourceL 2 (^#(0 : V)) := by simp
  have hw1 : IsSemitermVec SourceL 1 1 (?[^#(0 : V)] : V) := by simp
  have hw2 : IsSemitermVec SourceL 2 3 (?[^#(1 : V),^#(2 : V)] : V) := by simp; norm_num
  have hw3 : IsSemitermVec SourceL 2 3 (?[^#(1 : V),^#(0 : V)] : V) := by simp
  have hd : subst SourceL (?[^#(0 : V)] : V) (domainCode (^#(0 : V))) = domainCode (^#(0 : V)) := by
    rw [domainCode_subst h0 hw1]
    simp
  have hv : subst SourceL (?[^#(1 : V),^#(2 : V)] : V) (variableValue (^#(0 : V)) (^#(1 : V))) =
      variableValue (^#(1 : V)) (^#(2 : V)) := by
    rw [variableValue_subst h2 h1 hw2]
    simp
  have hi : subst SourceL (?[^#(1 : V),^#(0 : V)] : V) (orderIsoCode (^#(0 : V)) (^#(1 : V))) =
      orderIsoCode (^#(1 : V)) (^#(0 : V)) := by
    rw [orderIsoCode_subst h2 h1 hw3]
    simp
  have hid : subst SourceL (?[^#(0 : V)] : V) (valBody s) = valBody s := by
    exact subst_eq_self (valBody_valid hs) (by simp) (fun i hi => by
      have h : i = 0 := by simpa using hi
      subst i
      simp)
  rw [hd,hv,hi,hid]
  simp only [substs1,hid,eqForm,imp]
#print axioms instance_code
end generic
end PA194NameValueSchema
