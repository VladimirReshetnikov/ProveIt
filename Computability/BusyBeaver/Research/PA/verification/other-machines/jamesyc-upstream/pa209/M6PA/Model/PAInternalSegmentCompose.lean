module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalTraceCompose
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] Step StepFormula.formula
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma segment_compose {q0 l0 r0 n m qs ls rs q l r qys lys rys q' l' r' : V}
    (hp : Segment n qs ls rs q0 l0 r0 q l r)
    (hs : Segment m qys lys rys q l r q' l' r') :
    ∃ qzs lzs rzs, Segment (n+m) qzs lzs rzs q0 l0 r0 q' l' r' := by
  rcases hp with ⟨hq,hl,hr,hq0,hl0,hr0,hqn,hln,hrn,hsteps⟩
  rcases hs with ⟨hqy,hly,hry,hqy0,hly0,hry0,hqym,hlym,hrym,ysteps⟩
  obtain ⟨aq,qt,rfl⟩ := exists_adjoin_of_len_succ hqy
  obtain ⟨al,lt,rfl⟩ := exists_adjoin_of_len_succ hly
  obtain ⟨ar,rt,rfl⟩ := exists_adjoin_of_len_succ hry
  simp only [nth_adjoin_zero] at hqy0 hly0 hry0
  subst aq; subst al; subst ar
  have hqt : len qt = m := add_right_cancel (by simpa only [len_adjoin] using hqy)
  have hlt : len lt = m := add_right_cancel (by simpa only [len_adjoin] using hly)
  have hrt : len rt = m := add_right_cancel (by simpa only [len_adjoin] using hry)
  have oq {i : V} (hi : i < n+1) : nth (HFSAppend.append qs qt) i = nth qs i :=
    HFSAppend.nth_append_left qs qt (by simpa [hq] using hi)
  have ol {i : V} (hi : i < n+1) : nth (HFSAppend.append ls lt) i = nth ls i :=
    HFSAppend.nth_append_left ls lt (by simpa [hl] using hi)
  have orr {i : V} (hi : i < n+1) : nth (HFSAppend.append rs rt) i = nth rs i :=
    HFSAppend.nth_append_left rs rt (by simpa [hr] using hi)
  have jq := append_overlap qs qt n q hq hqn
  have jl := append_overlap ls lt n l hl hln
  have jr := append_overlap rs rt n r hr hrn
  refine ⟨HFSAppend.append qs qt,HFSAppend.append ls lt,HFSAppend.append rs rt,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [hq,hqt,add_assoc,add_comm,add_left_comm]
  · simp [hl,hlt,add_assoc,add_comm,add_left_comm]
  · simp [hr,hrt,add_assoc,add_comm,add_left_comm]
  · exact (oq (by simp)).trans hq0
  · exact (ol (by simp)).trans hl0
  · exact (orr (by simp)).trans hr0
  · exact (jq m).trans hqym
  · exact (jl m).trans hlym
  · exact (jr m).trans hrym
  · intro i hi
    by_cases hin : i < n
    · have hin0 : i < n+1 := lt_trans hin (by simp)
      have hin1 : i+1 < n+1 := by simpa using hin
      simpa only [oq hin0,ol hin0,orr hin0,oq hin1,ol hin1,orr hin1] using hsteps i hin
    · obtain ⟨j,rfl⟩ := exists_add_of_le (le_of_not_gt hin)
      have hj : j < m := by simpa using hi
      simpa only [add_assoc,jq,jl,jr] using ysteps j hj

end Models

def segmentCompositionSentence : ArithmeticSentence :=
  “∀ n m qs ls rs qys lys rys q0 l0 r0 q l r q' l' r',
    !segmentFormula n qs ls rs q0 l0 r0 q l r ∧
    !segmentFormula m qys lys rys q l r q' l' r' →
    ∃ qzs lzs rzs, !segmentFormula (n+m) qzs lzs rzs q0 l0 r0 q' l' r'”

theorem pa_proves_segment_composition : theory ⊢ segmentCompositionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [segmentCompositionSentence,models_iff]
  simp [segment_correct]
  intro n m qs ls rs qys lys rys q0 l0 r0 q l r q' l' r' hp hs
  exact segment_compose hp hs

#print axioms segment_compose
#print axioms pa_proves_segment_composition
end M6.Arithmetic.PA.InternalTrace

