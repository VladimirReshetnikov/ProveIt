module
/- Exact PA196 zipper and arithmetic-tape correspondence. -/
public import PA196.Arithmetic.Machine.Exact.PANativeTable
@[expose] public section
namespace PA196.Arithmetic.Machine.Exact.PaddedBridge
open M6.Zip PA196.Arithmetic.Machine.Exact.NativeTable PA196.Literal
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
/-- The exact 196-state arithmetic table presented as a natural-label zipper machine. -/
def machine : TMN := fun q b =>
  (inverse q).map fun d =>
    let a := row d b
    (a.write,a.right,labelControl a.next)
def Live (q : Nat) : Prop := q=196 ∨ q∈workingLabels
instance (q : Nat) : Decidable (Live q) := inferInstanceAs (Decidable (_ ∨ _))
private theorem agree_rows : workingLabels.all (fun q =>
    decide (machine q false=PA196.Literal.machine q false) &&
    decide (machine q true=PA196.Literal.machine q true))=true := by decide +kernel

theorem agree {q : Nat} (hq : Live q) (b : Bool) : machine q b=PA196.Literal.machine q b := by
  rcases hq with rfl|hq
  · cases b <;> decide +kernel
  · have h := List.all_eq_true.mp agree_rows q hq
    cases b
    · exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    · exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

private theorem next_live {q q' : Nat} {b w dir : Bool}
    (h : PA196.Literal.machine q b=some (w,dir,q')) : Live q' := by
  have hq := StateBound.domain (b := b) (by intro hn; exact Option.some_ne_none _ (h.symm.trans hn))
  have hr := List.all_eq_true.mp StateBound.all_rows_closed q hq
  have hb : StateBound.rowClosed q b=true := by
    cases b
    · exact (Bool.and_eq_true_iff.mp hr).1
    · exact (Bool.and_eq_true_iff.mp hr).2
  unfold StateBound.rowClosed at hb
  rw [h] at hb
  exact of_decide_eq_true hb

private theorem step_agree {c : Conf} (hc : Live c.q) :
    step machine c=step PA196.Literal.machine c := by
  unfold step
  rw [agree hc]

private theorem step_live {c d : Conf} (h : step PA196.Literal.machine c=some d) : Live d.q := by
  cases hm : PA196.Literal.machine c.q (c.r.headD false) with
  | none => simp only [step,hm,reduceCtorEq] at h
  | some a =>
    rcases a with ⟨w,dir,q⟩
    have hq := next_live hm
    cases dir <;> simp only [step,hm,Option.some.injEq] at h <;> subst d <;> exact hq

theorem run_agree (n : Nat) (c : Conf) (hc : Live c.q) :
    run machine n c=run PA196.Literal.machine n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run,step_agree hc]
    cases hs : step PA196.Literal.machine c with
    | none => rfl
    | some c' => exact ih c' (step_live hs)

private theorem run_live (n : Nat) {c d : Conf} (hc : Live c.q)
    (h : run PA196.Literal.machine n c=some d) : Live d.q := by
  induction n generalizing c with
  | zero => simp only [run,Option.some.injEq] at h; subst d; exact hc
  | succ n ih =>
    cases hs : step PA196.Literal.machine c with
    | none => simp only [run,hs,reduceCtorEq] at h
    | some c' => exact ih (step_live hs) (by simpa only [run,hs] using h)

theorem halts_iff (c : Conf) (hc : Live c.q) :
    Halts machine c ↔ Halts PA196.Literal.machine c := by
  constructor
  · rintro ⟨d,⟨n,hn⟩,hd⟩
    rw [run_agree n c hc] at hn
    exact ⟨d,⟨n,hn⟩,(step_agree (run_live n hc hn)).symm.trans hd⟩
  · rintro ⟨d,⟨n,hn⟩,hd⟩
    exact ⟨d,⟨n,(run_agree n c hc).trans hn⟩,(step_agree (run_live n hc hn)).trans hd⟩
#print axioms halts_iff
end PA196.Arithmetic.Machine.Exact.PaddedBridge
