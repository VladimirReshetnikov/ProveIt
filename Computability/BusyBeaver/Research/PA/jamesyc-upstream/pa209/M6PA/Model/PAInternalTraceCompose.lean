module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalTraceAppend
@[expose] public section

namespace M6.Arithmetic.PA.InternalTrace
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
attribute [local irreducible] StepFormula.formula Step

/-- A normalized segment with arbitrary, explicitly specified initial state. -/
def segmentFormula : ArithmeticSemisentence 10 :=
  “n qs ls rs q0 l0 r0 q l r.
    !lenDef (n+1) qs ∧ !lenDef (n+1) ls ∧ !lenDef (n+1) rs ∧
    !nthDef q0 qs 0 ∧ !nthDef l0 ls 0 ∧ !nthDef r0 rs 0 ∧
    !nthDef q qs n ∧ !nthDef l ls n ∧ !nthDef r rs n ∧
    ∀ i < n, ∃ a b c a' b' c',
      !nthDef a qs i ∧ !nthDef b ls i ∧ !nthDef c rs i ∧
      !nthDef a' qs (i+1) ∧ !nthDef b' ls (i+1) ∧
      !nthDef c' rs (i+1) ∧ !StepFormula.formula a b c a' b' c'”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def Segment (n qs ls rs q0 l0 r0 q l r : V) : Prop :=
  len qs = n+1 ∧ len ls = n+1 ∧ len rs = n+1 ∧
  nth qs 0 = q0 ∧ nth ls 0 = l0 ∧ nth rs 0 = r0 ∧
  nth qs n = q ∧ nth ls n = l ∧ nth rs n = r ∧
  ∀ i < n, Step (nth qs i) (nth ls i) (nth rs i)
    (nth qs (i+1)) (nth ls (i+1)) (nth rs (i+1))

lemma segment_correct (b : Fin 10 → V) :
    (V ⊧/b segmentFormula) ↔
      Segment (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) (b 6) (b 7) (b 8) (b 9) := by
  simp only [segmentFormula]
  simp [Segment,nth_defined.df,len_defined.df,step_vector,eq_comm]

lemma segment_one {q l r q' l' r' : V} (h : Step q l r q' l' r') :
    Segment 1 ?[q,q'] ?[l,l'] ?[r,r'] q l r q' l' r' := by
  simpa [Segment,lt_one_iff_eq_zero] using h

lemma exists_adjoin_of_len_succ {xs n : V} (h : len xs = n+1) :
    ∃ a tail, xs = a ∷ tail := by
  rcases nil_or_adjoin xs with hz | ha
  · have hp : 0 < len xs := by rw [h]; simp
    simp [hz] at hp
  · exact ha

lemma append_overlap (xs tail n q : V) (hl : len xs = n+1)
    (he : nth xs n = q) (j : V) :
    nth (HFSAppend.append xs tail) (n+j) = nth (q ∷ tail) j := by
  rcases zero_or_succ j with rfl | ⟨j,rfl⟩
  · simpa [he] using HFSAppend.nth_append_left xs tail (i := n) (by rw [hl]; simp)
  · rw [show n+(j+1) = len xs+j by rw [hl]; ac_rfl,
      HFSAppend.nth_append_right,nth_adjoin_succ]

/-- Joining removes exactly the duplicated initial entry of the second segment. -/
lemma prefix_compose {n m qs ls rs q l r qys lys rys q' l' r' : V}
    (hp : Prefix n qs ls rs q l r)
    (hs : Segment m qys lys rys q l r q' l' r') :
    ∃ qzs lzs rzs, Prefix (n+m) qzs lzs rzs q' l' r' := by
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

def oneSegmentSentence : ArithmeticSentence :=
  “∀ q l r q' l' r', !StepFormula.formula q l r q' l' r' →
    ∃ qs ls rs, !segmentFormula 1 qs ls rs q l r q' l' r'”

theorem pa_proves_one_segment : theory ⊢ oneSegmentSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [oneSegmentSentence,models_iff]
  simp [segment_correct,step_vector]
  intro q l r q' l' r' h
  exact ⟨?[q,q'],?[l,l'],?[r,r'],segment_one h⟩

def compositionSentence : ArithmeticSentence :=
  “∀ n m qs ls rs qys lys rys q l r q' l' r',
    !prefixFormula n qs ls rs q l r ∧ !segmentFormula m qys lys rys q l r q' l' r' →
    ∃ qzs lzs rzs, !prefixFormula (n+m) qzs lzs rzs q' l' r'”

theorem pa_proves_composition : theory ⊢ compositionSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [compositionSentence,models_iff]
  simp [prefix_correct,segment_correct]
  intro n m qs ls rs qys lys rys q l r q' l' r' hp hs
  exact prefix_compose hp hs

#print axioms pa_proves_one_segment
#print axioms pa_proves_composition
end M6.Arithmetic.PA.InternalTrace

