module
public import M6.Source.Determinism

/-! Explicit global-driver convention: a normal source-root return restarts
ordinal zero in the same primitive step. Explicit halt remains halt. -/
@[expose] public section

namespace M6.Source

def restart (c : Configuration) : Configuration :=
  match c.control with
  | .exited => ⟨.at 0,c.registers⟩
  | _ => c

def cycleStep (sites : Array Site) (c : Configuration) : Configuration :=
  restart (step sites c)

inductive CycleSteps (sites : Array Site) : Nat → Configuration → Configuration → Prop
  | refl (c) : CycleSteps sites 0 c c
  | cons : CycleSteps sites n (cycleStep sites a) b → CycleSteps sites (n+1) a b

theorem restart_eq_of_ne (h : c.control ≠ .exited) : restart c = c := by
  rcases c with ⟨q,r⟩
  cases q <;> simp_all [restart]

private theorem exited_stable (h : c.control = .exited) : step sites c = c := by
  rcases c with ⟨q,r⟩
  cases q <;> simp_all [step]

/-- A finite normal-return invocation supplies a positive finite cyclic segment.
Its length may be shorter only because an invocation proof can contain redundant
absorbing exit stutters; those are never transferred to the cyclic driver. -/
theorem normal_to_cycle (h : Steps sites n a b)
    (ha : a.control ≠ .exited) (hb : b.control = .exited) :
    ∃ m, 0 < m ∧ m ≤ n ∧ CycleSteps sites m a (restart b) := by
  induction h with
  | refl => exact False.elim (ha hb)
  | @cons n a b h ih =>
    by_cases he : (step sites a).control = .exited
    · have hs := exited_stable (sites := sites) he
      have heq : step sites a = b := (run_stable hs n).symm.trans h.eq_run
      refine ⟨1, by omega, by omega, ?_⟩
      apply CycleSteps.cons
      change CycleSteps sites 0 (restart (step sites a)) (restart b)
      rw [heq]
      exact CycleSteps.refl _
    · rcases ih he hb with ⟨m,hm,hmn,hsteps⟩
      refine ⟨m+1, by omega, by omega, ?_⟩
      apply CycleSteps.cons
      simpa only [cycleStep, restart_eq_of_ne he] using hsteps

/-- A halting invocation cannot have passed a normal absorbing return, so all
its primitive steps transport unchanged to the cyclic driver. -/
theorem halt_to_cycle (h : Steps sites n a b) (hb : b.control = .halted) :
    CycleSteps sites n a b := by
  induction h with
  | refl => exact CycleSteps.refl _
  | @cons n a b h ih =>
    have he : (step sites a).control ≠ .exited := by
      intro hx
      have hs := exited_stable (sites := sites) hx
      have heq : step sites a = b := (run_stable hs n).symm.trans h.eq_run
      rw [heq, hb] at hx
      cases hx
    apply CycleSteps.cons
    simpa only [cycleStep, restart_eq_of_ne he] using ih hb

#print axioms normal_to_cycle
#print axioms halt_to_cycle
end M6.Source

