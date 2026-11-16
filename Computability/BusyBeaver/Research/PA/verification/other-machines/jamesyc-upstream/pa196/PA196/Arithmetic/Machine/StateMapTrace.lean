module
public import PA196.Arithmetic.Machine.StateMap
public import PA196.Arithmetic.Machine.Exact.PAHaltingFormula
@[expose] public section
namespace PA196.Arithmetic.Machine.StateMap
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
open PA PA.InternalTrace

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

def NotPadding (q : V) : Prop :=
  q≠188 ∧ q≠189 ∧ q≠190 ∧ q≠191 ∧ q≠194 ∧ q≠195 ∧ q≠197 ∧ q≠198 ∧
  q≠200 ∧ q≠201 ∧ q≠204 ∧ q≠205 ∧ q≠206 ∧ q≠207 ∧ q≠208 ∧ q≠209 ∧
  q≠210 ∧ q≠212 ∧ q≠214

private theorem disjoin_cases (rs : List (WorkingState × Bool)) (v : Fin 6 → V) :
    (V ⊧/v (StepFormula.disjoin rs)) ↔ ∃ p∈rs,V ⊧/v (StepFormula.rowFormula p.1 p.2) := by
  induction rs with
  | nil => simp [StepFormula.disjoin]
  | cons p rs ih =>
    rcases p with ⟨s,b⟩
    simp [StepFormula.disjoin,ih]

private theorem exact_disjoin_cases (rs : List (Exact.WorkingState × Bool)) (v : Fin 6 → V) :
    (V ⊧/v (Exact.PA.StepFormula.disjoin rs)) ↔
      ∃ p∈rs,V ⊧/v (Exact.PA.StepFormula.rowFormula p.1 p.2) := by
  induction rs with
  | nil => simp [Exact.PA.StepFormula.disjoin]
  | cons p rs ih =>
    rcases p with ⟨s,b⟩
    simp [Exact.PA.StepFormula.disjoin,ih]

private theorem row_tags (s : WorkingState) (b : Bool) (q l r q' l' r' : V)
    (h : V ⊧/![q,l,r,q',l',r'] (StepFormula.rowFormula s b)) :
    q=(s.val : V) ∧ q'=(StepFormula.controlCode (row s b).next : V) := by
  cases hd : (row s b).right <;> simp [StepFormula.rowFormula,hd,numeral_eq_natCast] at h <;>
    exact ⟨h.1,h.2.1⟩

private theorem active_source {s : WorkingState} {q : V}
    (h : q=(s.val : V)) (hq : NotPadding q) : active s := by
  apply (active_iff s).mpr
  rw [h] at hq
  unfold NotPadding at hq
  unfold NotPaddingNat
  exact_mod_cast hq

private theorem step_preserves (q l r q' l' r' : V)
    (h : Step q l r q' l' r') (hq : NotPadding q) : NotPadding q' := by
  obtain ⟨⟨s,b⟩,_,hr⟩ := (disjoin_cases StepFormula.rows _).mp h
  obtain ⟨hs,ht⟩ := row_tags s b _ _ _ _ _ _ hr
  have ha := target_not_padding s b (active_source hs hq)
  rw [ht]
  unfold NotPadding
  unfold NotPaddingNat at ha
  exact_mod_cast ha

private theorem row_maps (s : Exact.WorkingState) (b : Bool) (q l r q' l' r' : V)
    (h : V ⊧/![q,l,r,q',l',r'] (StepFormula.rowFormula (auxState s) b)) :
    V ⊧/![decodeTag q,l,r,decodeTag q',l',r'] (Exact.PA.StepFormula.rowFormula s b) := by
  obtain ⟨hs,ht⟩ := row_tags (auxState s) b _ _ _ _ _ _ h
  have hds : decodeTag q=(s.val : V) := by
    rw [hs]
    exact decode_aux_control (some s)
  have hdt : decodeTag q'=(Exact.PA.StepFormula.controlCode (Exact.row s b).next : V) := by
    rw [ht,row_binding]
    exact decode_aux_control (Exact.row s b).next
  cases hd : (Exact.row s b).right <;>
    simp only [StepFormula.rowFormula,row_binding,hd,Bool.false_eq_true,
      if_false,if_true,Exact.PA.StepFormula.rowFormula] at h ⊢ <;>
    simp [numeral_eq_natCast,hds,hdt] at h ⊢ <;> exact h.2.2

theorem step_maps (q l r q' l' r' : V)
    (h : Step q l r q' l' r') (hq : NotPadding q) :
    V ⊧/![decodeTag q,l,r,decodeTag q',l',r'] Exact.PA.StepFormula.formula := by
  obtain ⟨⟨s,b⟩,_,hr⟩ := (disjoin_cases StepFormula.rows _).mp h
  have ha := active_source (row_tags s b _ _ _ _ _ _ hr).1 hq
  obtain ⟨a,rfl⟩ := aux_complete s ha
  apply (exact_disjoin_cases Exact.PA.StepFormula.rows _).mpr
  refine ⟨(a,b),?_,row_maps a b _ _ _ _ _ _ hr⟩
  cases b <;> simp [Exact.PA.StepFormula.rows]

attribute [local irreducible] Step StepFormula.formula Exact.PA.StepFormula.formula

theorem segment_avoids_padding {n qs ls rs lf rf : V}
    (h : Segment n qs ls rs 0 0 0 215 lf rf) :
    ∀ i : V,i≤n → NotPadding (nth qs i) := by
  intro i
  induction i using ISigma1.sigma1_succ_induction
  · unfold NotPadding
    definability
  case zero => intro _; simp [NotPadding,h.2.2.2.1]
  case succ i ih =>
    intro hi
    have hn : i<n := lt_of_lt_of_le (by simp) hi
    exact step_preserves _ _ _ _ _ _ (h.2.2.2.2.2.2.2.2.2 i hn) (ih (le_of_lt hn))

end Models
#print axioms step_maps
#print axioms segment_avoids_padding
end PA196.Arithmetic.Machine.StateMap
