import PA194PAeqClosureClosed
import PA194TermDispatcherEquations
import PA194TermScope
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194ClosedEnvironment
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194PAeqBind
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def SameTermContext (P Q : V) : Prop := nth P 0 = nth Q 0 ∧ nth P 2 = nth Q 2

theorem sameChild {P Q : V} (h : SameTermContext P Q) :
    SameTermContext (childParameters P) (childParameters Q) := by
  simp only [SameTermContext,childParameters,parameters_bound,parameters_result,h.1, and_self]

theorem sameBinary {P Q : V} (h : SameTermContext P Q) (i : V) :
    SameTermContext (binaryParameters P i) (binaryParameters Q i) := by
  simp only [SameTermContext,binaryParameters,parameters_bound,parameters_result,h.1, and_self]

def ClosedTermProperty (t : V) : Prop :=
  ∀ P Q, SameTermContext P Q → termFreeBound t = 0 → translate P t = translate Q t

theorem closedTermProperty_definable : 𝚷₁-Predicate (ClosedTermProperty : V → Prop) := by
  haveI : 𝚺₁-Function₁ (termFreeBound : V → V) := termFreeBound_defined.to_definable
  haveI : 𝚺₁-Function₂ (translate : V → V → V) := translate_defined.to_definable
  unfold ClosedTermProperty SameTermContext
  definability

theorem closedTermEnvironment {t : V} (ht : IsUTerm PA194PAeq.language t) : ClosedTermProperty t := by
  apply IsUTerm.induction 𝚷 closedTermProperty_definable ?_ ?_ ?_ t ht
  · intro i P Q h hz
    simp only [translate_bound,h.1,h.2]
  · intro i P Q h hz
    simp at hz
  · intro k f v hf hv ih P Q h hz
    have hmax : listMax (termFreeBoundVec k v) = 0 := by simpa [termFreeBound_func hf hv] using hz
    have hchild : ∀ i < k, termFreeBound (nth v i) = 0 := by
      intro i hi
      apply le_antisymm _ zero_le
      have hle := nth_le_listMax (v := termFreeBoundVec k v) (by simpa [termFreeBoundVec_len hv] using hi)
      simpa [termFreeBoundVec_nth hv hi,hmax] using hle
    rcases (PA194PAeq.source_functions k f).mp hf with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,htwo⟩
    · have hv0 : v = 0 := len_zero_iff_eq_nil.mp hv.lh.symm
      subst v
      simp only [translate_zero,h.2]
    · obtain ⟨a,rfl⟩ := eq_singleton_iff_len_eq_one.mp hv.lh.symm
      have ha : IsUTerm PA194PAeq.language a := by simpa using hv.2 0 (by simp)
      have hza : termFreeBound a = 0 := by simpa using hchild 0 (by simp)
      have he : translate (childParameters P) a = translate (childParameters Q) a := by
        simpa using ih 0 (by simp) (childParameters P) (childParameters Q) (sameChild h) (by simpa using hza)
      rw [translate_succ P a ha,translate_succ Q a ha,h.2,he]
    · obtain ⟨a,b,rfl⟩ := eq_doubleton_of_len_eq_two.mp hv.lh.symm
      have ha : IsUTerm PA194PAeq.language a := by simpa using hv.2 0 (by simp)
      have hb : IsUTerm PA194PAeq.language b := by simpa using hv.2 1 (by simp)
      have hza : termFreeBound a = 0 := by simpa using hchild 0 (by simp)
      have hzb : termFreeBound b = 0 := by simpa using hchild 1 (by simp)
      have hea : translate (binaryParameters P 1) a = translate (binaryParameters Q 1) a := by
        simpa using ih 0 (by simp) (binaryParameters P 1) (binaryParameters Q 1) (sameBinary h 1) (by simpa using hza)
      have heb : translate (binaryParameters P 0) b = translate (binaryParameters Q 0) b := by
        simpa using ih 1 (by simp) (binaryParameters P 0) (binaryParameters Q 0) (sameBinary h 0) (by simpa using hzb)
      rcases htwo with rfl | rfl
      · rw [translate_add P a b ha hb,translate_add Q a b ha hb,h.2,hea,heb]
      · rw [translate_mul P a b ha hb,translate_mul Q a b ha hb,h.2,hea,heb]
#print axioms closedTermProperty_definable
#print axioms closedTermEnvironment
end generic
end PA194ClosedEnvironment
