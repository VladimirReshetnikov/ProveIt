import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194BindAllTerm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
def blueprint : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z depth. !qqBvarDef y z”
  fvar := .mkSigma “y x depth. !qqBvarDef y (depth+x)”
  func := .mkSigma “y k f v v' depth. !qqFuncDef y k f v'”
noncomputable def construction : Language.TermRec.Construction V blueprint where
  bvar _ z := ^#z
  fvar p x := ^#(p 0+x)
  func _ k f _ v' := ^func k f v'
  bvar_defined := .mk fun v => by simp [blueprint]
  fvar_defined := .mk fun v => by simp [blueprint]
  func_defined := .mk fun v => by simp [blueprint]
noncomputable def bindAll (d t : V) : V := construction.result ℒₒᵣ ![d] t
noncomputable def bindAllVec (d k v : V) : V := construction.resultVec ℒₒᵣ ![d] k v
@[simp] theorem bindAll_bvar (d z : V) : bindAll d (^#z) = ^#z := by simp [bindAll,construction]
@[simp] theorem bindAll_fvar (d x : V) : bindAll d (^&x) = ^#(d+x) := by simp [bindAll,construction]
theorem bindAll_func (d k f v : V) (hf : (ℒₒᵣ : Language).IsFunc k f) (hv : IsUTermVec ℒₒᵣ k v) :
    bindAll d (^func k f v) = ^func k f (bindAllVec d k v) := by
  simp [bindAll,bindAllVec,construction,hf,hv]
instance bindAll_definable : 𝚺₁-Function₂ (bindAll (V := V)) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 2 → V => construction.result ℒₒᵣ (v ·.succ) (v 0)) :=
    construction.result_defined.to_definable
  have hi : ∀ j : Fin 2, 𝚺₁.DefinableFunction (fun v : Fin 2 → V => ![v 1,v 0] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 1
    · exact Fin.cases (HierarchySymbol.DefinableFunction.var 0) (fun x => Fin.elim0 x) k
  have hh := HierarchySymbol.DefinableFunction.substitution hg hi
  change 𝚺₁.DefinableFunction (fun v : Fin 2 → V => bindAll (v 0) (v 1))
  convert hh using 1
  funext v
  unfold bindAll
  congr 1
lemma bindAll_isUTerm (d t : V) (ht : IsUTerm ℒₒᵣ t) : IsUTerm ℒₒᵣ (bindAll d t) := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [bindAll_func d k f v hf hv]
    apply IsUTerm.func_iff.mpr
    refine ⟨hf,?_⟩
    refine ⟨?_,?_⟩
    · simp [bindAllVec,hv]
    · intro i hi
      rw [show (bindAllVec d k v).[i] = bindAll d v.[i] by
        exact Language.TermRec.Construction.nth_resultVec _ _ _ hv hi]
      exact ih i hi
lemma bindAllVec_isUTerm (d k v : V) (hv : IsUTermVec ℒₒᵣ k v) :
    IsUTermVec ℒₒᵣ k (bindAllVec d k v) := by
  refine ⟨?_,?_⟩
  · simp [bindAllVec,hv]
  · intro i hi
    rw [show (bindAllVec d k v).[i] = bindAll d v.[i] by
      exact Language.TermRec.Construction.nth_resultVec _ _ _ hv hi]
    exact bindAll_isUTerm d _ (hv.nth hi)

lemma bindAll_shift_fixed (d t : V) (ht : IsUTerm ℒₒᵣ t) :
    termShift ℒₒᵣ (bindAll d t) = bindAll d t := by
  apply IsUTerm.induction 𝚺 ?_ ?_ ?_ ?_ t ht
  · definability
  · intro z; simp
  · intro x; simp
  · intro k f v hf hv ih
    rw [bindAll_func d k f v hf hv,termShift_func hf (bindAllVec_isUTerm d k v hv)]
    congr 1
    apply nth_ext' k
    · simp [bindAllVec_isUTerm d k v hv]
    · simp [bindAllVec,hv]
    · intro i hi
      rw [nth_termShiftVec (bindAllVec_isUTerm d k v hv) hi]
      rw [show (bindAllVec d k v).[i] = bindAll d v.[i] by
        exact Language.TermRec.Construction.nth_resultVec _ _ _ hv hi]
      exact ih i hi
lemma bindAll_decode (d N t w : V) (ht : IsSemiterm ℒₒᵣ d t)
    (hout : IsSemiterm ℒₒᵣ (d+N) (bindAll d t))
    (hbound : ∀ z < d, w.[z] = ^#z)
    (hfree : ∀ x < N, w.[d+x] = ^&x) :
    termSubst ℒₒᵣ w (bindAll d t) = t := by
  have hd : 𝚺₁-Predicate (fun t : V => IsSemiterm ℒₒᵣ (d+N) (bindAll d t) → termSubst ℒₒᵣ w (bindAll d t) = t) := by definability
  revert hout
  apply IsSemiterm.induction 𝚺 hd ?_ ?_ ?_ t ht
  · intro z hz _
    simp [hbound z hz]
  · intro x hx
    have hxN : x < N := by
      have hh : d+x < d+N := by simpa using hx
      exact (add_lt_add_iff_left d).mp hh
    simp [hfree x hxN]
  · intro k f v hf hv ih ho
    rw [bindAll_func d k f v hf hv.isUTerm] at ho ⊢
    have houtvec : IsSemitermVec ℒₒᵣ k (d+N) (bindAllVec d k v) := (IsSemiterm.func.mp ho).2
    rw [termSubst_func hf houtvec.isUTerm]
    congr 1
    apply nth_ext' k
    · simp [houtvec.isUTerm]
    · exact hv.lh
    · intro i hi
      rw [nth_termSubstVec houtvec.isUTerm hi]
      rw [show (bindAllVec d k v).[i] = bindAll d v.[i] by
        exact Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
      exact ih i hi (by
        have hh := houtvec.nth hi
        rw [show (bindAllVec d k v).[i] = bindAll d v.[i] by
          exact Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi] at hh
        exact hh)
#print axioms bindAll_decode
#print axioms bindAll_shift_fixed
#print axioms bindAll_isUTerm
end PA194BindAllTerm
