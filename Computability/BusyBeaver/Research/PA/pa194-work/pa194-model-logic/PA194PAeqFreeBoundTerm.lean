import PA194PAeqClosure
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeqBind
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def termFreeBlueprint : Language.TermRec.Blueprint 0 where
  bvar := .mkSigma “out i. out = 0”
  fvar := .mkSigma “out i. out = i+1”
  func := .mkSigma “out ar f v w. !listMaxDef out w”
noncomputable def termFreeConstruction : Language.TermRec.Construction V termFreeBlueprint where
  bvar _ _ := 0
  fvar _ i := i+1
  func _ _ _ _ w := listMax w
  bvar_defined := .mk fun v => by simp [termFreeBlueprint]
  fvar_defined := .mk fun v => by simp [termFreeBlueprint]
  func_defined := .mk fun v => by simp [termFreeBlueprint]
noncomputable def termFreeBound (t : V) : V := termFreeConstruction.result PA194PAeq.language ![] t
noncomputable def termFreeBoundVec (ar v : V) : V := termFreeConstruction.resultVec PA194PAeq.language ![] ar v
noncomputable def termFreeBoundGraph : 𝚺₁.Semisentence 2 := termFreeBlueprint.result PA194PAeq.language
noncomputable def termFreeBoundVecGraph : 𝚺₁.Semisentence 3 := termFreeBlueprint.resultVec PA194PAeq.language
instance termFreeBound_defined : 𝚺₁-Function₁ (termFreeBound : V → V) via termFreeBoundGraph := .mk fun v => by
  have hempty : (fun _ : Fin 0 => v 1) = (![] : Fin 0 → V) := Subsingleton.elim _ _
  simpa [termFreeBoundGraph,termFreeBound,hempty] using termFreeConstruction.result_defined.defined v
instance termFreeBoundVec_defined : 𝚺₁-Function₂ (termFreeBoundVec : V → V → V) via termFreeBoundVecGraph := .mk fun v => by
  have hempty : (fun _ : Fin 0 => v 2) = (![] : Fin 0 → V) := Subsingleton.elim _ _
  simpa [termFreeBoundVecGraph,termFreeBoundVec,hempty] using termFreeConstruction.resultVec_defined.defined v
@[simp] theorem termFreeBound_bvar (i : V) : termFreeBound (^#i) = 0 := by simp [termFreeBound,termFreeConstruction]
@[simp] theorem termFreeBound_fvar (i : V) : termFreeBound (^&i) = i+1 := by simp [termFreeBound,termFreeConstruction]
theorem termFreeBound_func {ar f v : V} (hf : PA194PAeq.language.IsFunc ar f)
    (hv : IsUTermVec PA194PAeq.language ar v) :
    termFreeBound (^func ar f v) = listMax (termFreeBoundVec ar v) := by simp [termFreeBound,termFreeBoundVec,termFreeConstruction,hf,hv]
@[simp] theorem termFreeBoundVec_nth {ar v i : V} (hv : IsUTermVec PA194PAeq.language ar v) (hi : i<ar) :
    nth (termFreeBoundVec ar v) i = termFreeBound (nth v i) :=
  termFreeConstruction.nth_resultVec PA194PAeq.language ![] hv hi
@[simp] theorem termFreeBoundVec_len {ar v : V} (hv : IsUTermVec PA194PAeq.language ar v) :
    len (termFreeBoundVec ar v) = ar := termFreeConstruction.resultVec_lh PA194PAeq.language ![] hv
#print axioms termFreeBound_defined
#print axioms termFreeBoundVec_defined
#print axioms termFreeBound_func
#print axioms termFreeBoundVec_nth
end generic
end PA194PAeqBind
