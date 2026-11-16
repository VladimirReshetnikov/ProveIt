module
/- Exact211: fresh physical interpretation of the unchanged original coded source. -/
public import M6PA.Model.PANativeTable
@[expose] public section
namespace M6.Arithmetic.PaddedBridge
open M6.Zip M6.Arithmetic.NativeTable M6.Table
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
/-- Auxiliary dense-tag completion. Tags50,122,150,157,205 and214 remain unreachable. -/
def machine : TMN := fun q b =>
  (inverse q).map fun d =>
    let a := row d b
    (a.write,a.right,labelControl a.next)
def Live (q : Nat) : Prop := q=254 ∨ q∈workingLabels
instance (q : Nat) : Decidable (Live q) := inferInstanceAs (Decidable (_ ∨ _))
private theorem agree_rows : workingLabels.all (fun q =>
    decide (machine q false=M6.Table.machine q false) &&
    decide (machine q true=M6.Table.machine q true))=true := by decide +kernel

theorem agree {q : Nat} (hq : Live q) (b : Bool) : machine q b=M6.Table.machine q b := by
  rcases hq with rfl|hq
  · cases b <;> decide +kernel
  · have h := List.all_eq_true.mp agree_rows q hq
    cases b
    · exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).1
    · exact of_decide_eq_true (Bool.and_eq_true_iff.mp h).2

private theorem next_live {q q' : Nat} {b w dir : Bool}
    (h : M6.Table.machine q b=some (w,dir,q')) : Live q' := by
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
    step machine c=step M6.Table.machine c := by
  unfold step
  rw [agree hc]

private theorem step_live {c d : Conf} (h : step M6.Table.machine c=some d) : Live d.q := by
  cases hm : M6.Table.machine c.q (c.r.headD false) with
  | none => simp only [step,hm,reduceCtorEq] at h
  | some a =>
    rcases a with ⟨w,dir,q⟩
    have hq := next_live hm
    cases dir <;> simp only [step,hm,Option.some.injEq] at h <;> subst d <;> exact hq

theorem run_agree (n : Nat) (c : Conf) (hc : Live c.q) :
    run machine n c=run M6.Table.machine n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run,step_agree hc]
    cases hs : step M6.Table.machine c with
    | none => rfl
    | some c' => exact ih c' (step_live hs)

private theorem run_live (n : Nat) {c d : Conf} (hc : Live c.q)
    (h : run M6.Table.machine n c=some d) : Live d.q := by
  induction n generalizing c with
  | zero => simp only [run,Option.some.injEq] at h; subst d; exact hc
  | succ n ih =>
    cases hs : step M6.Table.machine c with
    | none => simp only [run,hs,reduceCtorEq] at h
    | some c' => exact ih (step_live hs) (by simpa only [run,hs] using h)

theorem halts_iff (c : Conf) (hc : Live c.q) :
    Halts machine c ↔ Halts M6.Table.machine c := by
  constructor
  · rintro ⟨d,⟨n,hn⟩,hd⟩
    rw [run_agree n c hc] at hn
    exact ⟨d,⟨n,hn⟩,(step_agree (run_live n hc hn)).symm.trans hd⟩
  · rintro ⟨d,⟨n,hn⟩,hd⟩
    exact ⟨d,⟨n,(run_agree n c hc).trans hn⟩,(step_agree (run_live n hc hn)).trans hd⟩
#print axioms halts_iff
end M6.Arithmetic.PaddedBridge
