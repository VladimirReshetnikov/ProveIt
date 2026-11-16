module
/- Exact PA196 arithmetic semantics, with literal working labels 0..195. -/
public import PA196.Arithmetic.Machine.Exact.PAMachine
public import PA196.Arithmetic.Machine.Exact.SparseBound
@[expose] public section
namespace PA196.Arithmetic.Machine.Exact.NativeTable
open M6.Zip PA196.Literal
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
abbrev machine := PA196.Literal.machine
def label (q : WorkingState) : Nat := denseLabels.getD q.val 196
def labelControl : Control → Nat
  | none => 196
  | some q => label q
def inverse (q : Nat) : Option WorkingState := workingStates.find? (fun d => label d == q)
theorem inverse_label : ∀ q : WorkingState, inverse (label q)=some q := by decide +kernel
theorem inverse_labelControl (q : Control) : inverse (labelControl q)=q := by
  cases q with
  | none => decide +kernel
  | some q => exact inverse_label q
private def rowMatches (q : Nat) (b : Bool) : Bool :=
  match machine q b, inverse q with
  | none,_ => true
  | some (w,d,q'),some i => decide (row i b=⟨w,d,inverse q'⟩)
  | some _,none => false
private theorem bindings : workingLabels.all (fun q => rowMatches q false && rowMatches q true)=true := by decide +kernel
theorem row_of_native {q q' : Nat} {b w dir : Bool}
    (h : machine q b=some (w,dir,q')) :
    ∃ d : WorkingState, inverse q=some d ∧ row d b=⟨w,dir,inverse q'⟩ := by
  have hd : q ∈ workingLabels := PA196.Arithmetic.Machine.Exact.StateBound.domain (b := b) (by intro hn; exact Option.some_ne_none _ (h.symm.trans hn))
  have hb := List.all_eq_true.mp bindings q hd
  have hb' : rowMatches q b=true := by
    cases b
    · exact (Bool.and_eq_true_iff.mp hb).1
    · exact (Bool.and_eq_true_iff.mp hb).2
  cases hi : inverse q with
  | none => simp [rowMatches,h,hi] at hb'
  | some d =>
    refine ⟨d,rfl,?_⟩
    simpa only [rowMatches,h,hi,decide_eq_true_eq] using hb'
#print axioms row_of_native
end PA196.Arithmetic.Machine.Exact.NativeTable
