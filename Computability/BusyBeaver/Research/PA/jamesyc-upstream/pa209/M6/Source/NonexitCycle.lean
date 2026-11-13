module
public import M6.Source.CyclicDriver
@[expose] public section
namespace M6.Source
theorem nonexit_to_cycle (h : Steps sites n a b) (hb : b.control ≠ .exited) :
    CycleSteps sites n a b := by
  induction h with
  | refl => exact CycleSteps.refl _
  | @cons n a b h ih =>
    have he : (step sites a).control ≠ .exited := by
      intro hx
      have hs : step sites (step sites a) = step sites a := by
        rcases hz : step sites a with ⟨q,r⟩
        rw [hz] at hx
        simp only at hx
        subst q
        rfl
      have heq : step sites a = b := (run_stable hs n).symm.trans h.eq_run
      rw [heq] at hx
      exact hb hx
    apply CycleSteps.cons
    simpa only [cycleStep, restart_eq_of_ne he] using ih hb

#print axioms nonexit_to_cycle
end M6.Source

