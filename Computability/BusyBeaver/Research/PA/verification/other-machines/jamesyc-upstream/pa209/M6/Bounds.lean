module
public import M6.Literal
@[expose] public section
namespace M6.Bounds
open M6.Literal
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def rowClosed (q : Nat) (b : Bool) : Bool :=
  match machine q b with
  | none => false
  | some (_,_,q') => decide (q' = halt ∨ q' ∈ workingLabels)

theorem all_rows_closed : workingLabels.all (fun q => rowClosed q false && rowClosed q true) = true := by decide +kernel

theorem start_working : start ∈ workingLabels := by decide +kernel

theorem state_bound : workingLabels.length = 209 ∧ workingLabels.Nodup :=
  ⟨M6.Literal.working_count, M6.Literal.working_nodup⟩

private theorem outside (n : Nat) (b : Bool) : machine (n+216) b = none := by
  cases b <;> rfl

private theorem finite_domain : (List.range 216).all (fun q =>
    (! (machine q false).isSome || decide (q ∈ workingLabels)) &&
    (! (machine q true).isSome || decide (q ∈ workingLabels))) = true := by decide +kernel

theorem domain {q : Nat} {b : Bool} (h : machine q b ≠ none) : q ∈ workingLabels := by
  by_cases hq : q < 216
  · have hh := List.all_eq_true.mp finite_domain q (List.mem_range.mpr hq)
    have hm : (machine q b).isSome = true := Option.isSome_iff_ne_none.mpr h
    cases b
    · have hf := (Bool.and_eq_true_iff.mp hh).1
      simp only [hm,Bool.not_true,Bool.false_or] at hf
      exact of_decide_eq_true hf
    · have hf := (Bool.and_eq_true_iff.mp hh).2
      simp only [hm,Bool.not_true,Bool.false_or] at hf
      exact of_decide_eq_true hf
  · have he : q = (q-216)+216 := by omega
    rw [he,outside] at h
    exact False.elim (h rfl)

#print axioms domain
#print axioms state_bound
end M6.Bounds
