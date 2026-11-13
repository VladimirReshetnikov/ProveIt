module
/- Exact209:418 active rows, excluding six unreachable auxiliary tags. -/
public import M6PA.Model.PAInternalTraceRows
public import M6PA.Model.SentenceCorrectness
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Arithmetic.PA.ExactHaltingFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic

def rows : List (WorkingState × Bool) := StepFormula.rows.filter (fun p => decide (active p.1))
def formula : ArithmeticSemisentence 6 := StepFormula.disjoin rows
 theorem rows_count : rows.length=418 := by decide +kernel
 theorem working_count : activeStates.length=209 := active_count
 theorem literal_binding : ∀ (q : WorkingState), active q → ∀ b,
    M6.Table.machine (NativeTable.label q) b =
      some ((row q b).write,(row q b).right,NativeTable.labelControl (row q b).next) := by decide +kernel

private theorem target_not_padding : ∀ (q : WorkingState) (b : Bool), active q →
    StepFormula.controlCode (row q b).next≠50 ∧ StepFormula.controlCode (row q b).next≠122 ∧ StepFormula.controlCode (row q b).next≠150 ∧ StepFormula.controlCode (row q b).next≠157 ∧ StepFormula.controlCode (row q b).next≠205 ∧ StepFormula.controlCode (row q b).next≠214 := by decide +kernel

def trace (F : ArithmeticSemisentence 6) : ArithmeticSentence :=
  “∃ n qs ls rs,
    !nthDef 0 qs 0 ∧ !nthDef 0 ls 0 ∧ !nthDef 0 rs 0 ∧
    !nthDef 215 qs n ∧
    ∀ i < n, ∃ q l r q' l' r',
      !nthDef q qs i ∧ !nthDef l ls i ∧ !nthDef r rs i ∧
      !nthDef q' qs (i+1) ∧ !nthDef l' ls (i+1) ∧ !nthDef r' rs (i+1) ∧
      !F q l r q' l' r'”
def traceSentence : ArithmeticSentence := trace formula
def nonhaltingSentence : ArithmeticSentence := ∼traceSentence
 theorem auxiliary_trace : trace StepFormula.formula=HaltingFormula.traceSentence := rfl

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
def NotPadding (q : V) : Prop := q≠50 ∧ q≠122 ∧ q≠150 ∧ q≠157 ∧ q≠205 ∧ q≠214
private theorem disjoin_cases (rs : List (WorkingState × Bool)) (v : Fin 6 → V) :
    (V ⊧/v (StepFormula.disjoin rs)) ↔ ∃ p∈rs,V ⊧/v (StepFormula.rowFormula p.1 p.2) := by
  induction rs with
  | nil => simp [StepFormula.disjoin]
  | cons p rs ih =>
    rcases p with ⟨s,b⟩
    simp [StepFormula.disjoin,ih]

private theorem row_tags (s : WorkingState) (b : Bool) (q l r q' l' r' : V)
    (h : V ⊧/![q,l,r,q',l',r'] (StepFormula.rowFormula s b)) :
    q=(s.val : V) ∧ q'=(StepFormula.controlCode (row s b).next : V) := by
  cases hd : (row s b).right <;> simp [StepFormula.rowFormula,hd,numeral_eq_natCast] at h <;>
    exact ⟨h.1,h.2.1⟩
private theorem active_source {s : WorkingState} {q : V}
    (h : q=(s.val : V)) (hq : NotPadding q) : active s := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro hs; apply hq.1; simpa only [hs,Nat.cast_ofNat] using h
  · intro hs; apply hq.2.1; simpa only [hs,Nat.cast_ofNat] using h
  · intro hs; apply hq.2.2.1; simpa only [hs,Nat.cast_ofNat] using h
  · intro hs; apply hq.2.2.2.1; simpa only [hs,Nat.cast_ofNat] using h
  · intro hs; apply hq.2.2.2.2.1; simpa only [hs,Nat.cast_ofNat] using h
  · intro hs; apply hq.2.2.2.2.2; simpa only [hs,Nat.cast_ofNat] using h

private theorem step_preserves (q l r q' l' r' : V)
    (h : V ⊧/![q,l,r,q',l',r'] StepFormula.formula) (hq : NotPadding q) : NotPadding q' := by
  obtain ⟨⟨s,b⟩,_,hr⟩ := (disjoin_cases StepFormula.rows _).mp h
  obtain ⟨hs,ht⟩ := row_tags s b _ _ _ _ _ _ hr
  have ha := target_not_padding s b (active_source hs hq)
  rw [ht]
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact_mod_cast ha.1
  · exact_mod_cast ha.2.1
  · exact_mod_cast ha.2.2.1
  · exact_mod_cast ha.2.2.2.1
  · exact_mod_cast ha.2.2.2.2.1
  · exact_mod_cast ha.2.2.2.2.2

private theorem exact_step (q l r q' l' r' : V)
    (h : V ⊧/![q,l,r,q',l',r'] StepFormula.formula) (hq : NotPadding q) :
    V ⊧/![q,l,r,q',l',r'] formula := by
  obtain ⟨⟨s,b⟩,hm,hr⟩ := (disjoin_cases StepFormula.rows _).mp h
  have ha := active_source (row_tags s b _ _ _ _ _ _ hr).1 hq
  apply (disjoin_cases rows _).mpr
  exact ⟨(s,b),List.mem_filter.mpr ⟨hm,by simpa using ha⟩,hr⟩

private theorem auxiliary_step (q l r q' l' r' : V)
    (h : V ⊧/![q,l,r,q',l',r'] formula) :
    V ⊧/![q,l,r,q',l',r'] StepFormula.formula := by
  obtain ⟨p,hm,hr⟩ := (disjoin_cases rows _).mp h
  exact (disjoin_cases StepFormula.rows _).mpr ⟨p,(List.mem_filter.mp hm).1,hr⟩

def Step (F : ArithmeticSemisentence 6) (q l r q' l' r' : V) : Prop :=
  V ⊧/![q,l,r,q',l',r'] F
section TraceProof
attribute [local irreducible] Step

def Trace (F : ArithmeticSemisentence 6) (n qs ls rs : V) : Prop :=
  nth qs 0=0 ∧ nth ls 0=0 ∧ nth rs 0=0 ∧ nth qs n=215 ∧
    ∀ i<n, Step F (nth qs i) (nth ls i) (nth rs i) (nth qs (i+1)) (nth ls (i+1)) (nth rs (i+1))

private theorem trace_correct (F : ArithmeticSemisentence 6) :
    (V ⊧/![] (trace F)) ↔ ∃ n qs ls rs : V,Trace F n qs ls rs := by
  have hf (b : Fin 6 → V) : (V ⊧/b F) ↔ Step F (b 0) (b 1) (b 2) (b 3) (b 4) (b 5) := by
    have hb : b=![b 0,b 1,b 2,b 3,b 4,b 5] := by simp [funext_iff,Fin.forall_fin_succ]
    unfold Step
    exact iff_of_eq (congrArg (fun v => V ⊧/v F) hb)
  simp [trace,nth_defined.df,Trace,hf,eq_comm,numeral_eq_natCast]

end TraceProof

private theorem avoids_padding (n qs ls rs : V) (h : Trace StepFormula.formula n qs ls rs) :
    ∀ i : V,i≤n → NotPadding (nth qs i) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · unfold NotPadding
    definability
  case zero => intro _; simp [NotPadding,h.1]
  case succ i ih =>
    intro hi
    have hn : i<n := lt_of_lt_of_le (by simp) hi
    exact step_preserves _ _ _ _ _ _ (h.2.2.2.2 i hn) (ih (le_of_lt hn))

theorem trace_equivalent :
    (V ⊧/![] traceSentence) ↔ (V ⊧/![] HaltingFormula.traceSentence) := by
  rw [traceSentence,← auxiliary_trace,trace_correct,trace_correct]
  constructor
  · rintro ⟨n,qs,ls,rs,h⟩
    refine ⟨n,qs,ls,rs,h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
    intro i hi
    exact auxiliary_step _ _ _ _ _ _ (h.2.2.2.2 i hi)
  · rintro ⟨n,qs,ls,rs,h⟩
    refine ⟨n,qs,ls,rs,h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_⟩
    intro i hi
    exact exact_step _ _ _ _ _ _ (h.2.2.2.2 i hi) (avoids_padding n qs ls rs h i (le_of_lt hi))
end Models

theorem pa_proves_exact_to_auxiliary :
    theory ⊢ nonhaltingSentence 🡒 HaltingFormula.nonhaltingSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [models_iff,LogicalConnective.HomClass.map_imply,
    nonhaltingSentence,HaltingFormula.nonhaltingSentence,LogicalConnective.HomClass.map_neg]
  exact fun h hf => h (trace_equivalent.mpr hf)

theorem sentence_iff_physical_nonhalting :
    (Nat ⊧/![] nonhaltingSentence) ↔ ¬ M6.Zip.Halts M6.Table.machine (M6.Conjugacy.mapConf M6.Startup.blank) := by
  have h : (Nat ⊧/![] nonhaltingSentence) ↔ (Nat ⊧/![] HaltingFormula.nonhaltingSentence) := by
    simp only [nonhaltingSentence,HaltingFormula.nonhaltingSentence,LogicalConnective.HomClass.map_neg]
    change (¬ (Nat ⊧/![] traceSentence)) ↔ ¬ (Nat ⊧/![] HaltingFormula.traceSentence)
    exact not_congr (trace_equivalent (V := Nat))
  exact h.trans M6.Arithmetic.PA.sentence_iff_physical_nonhalting
#print axioms literal_binding
#print axioms pa_proves_exact_to_auxiliary
#print axioms sentence_iff_physical_nonhalting
end M6.Arithmetic.PA.ExactHaltingFormula
