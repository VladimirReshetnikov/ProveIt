module
public import M6.Source.ExactSource
public import M6.Source.Determinism
public import M6.Source.CyclicDeterminism
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

namespace M6.Source.SeedPrefix

def seed : Configuration :=
  ⟨.at 25, fun r => if r = 1 ∨ r = 2 then 1 else 0⟩

def intermediate : Configuration :=
  ⟨.at 68, fun r => if r = 2 then 6 else if r = 7 then 7 else 0⟩

def snapshot (c : Configuration) : Control × List Nat := (c.control,List.ofFn c.registers)

theorem trace_checked : snapshot (run exactSites 159 seed) = snapshot intermediate := by decide

private theorem snapshot_injective (a b : Configuration) (h : snapshot a = snapshot b) : a = b := by
  rcases a with ⟨qa,ra⟩
  rcases b with ⟨qb,rb⟩
  have hq := congrArg Prod.fst h
  have hr := congrArg Prod.snd h
  change qa = qb at hq
  have he : ra = rb := by
    funext i
    have hh := congrArg (fun xs => xs[i.val]?) hr
    simpa only [snapshot, List.getElem?_ofFn, dite_eq_left i.isLt, Option.some.injEq] using hh
  cases hq
  cases he
  rfl

private theorem run_steps (sites : Array Site) (n : Nat) (a : Configuration) :
    Steps sites n a (run sites n a) := by
  induction n generalizing a with
  | zero => exact Steps.refl _
  | succ n ih => exact Steps.cons (ih (step sites a))

/-- Exact159 primitive source steps connect the clean virtual AX seed to the
intermediate AX state reached by the independently checked physical startup. -/
theorem trace : Steps exactSites 159 seed intermediate := by
  have he := snapshot_injective _ _ trace_checked
  rw [← he]
  exact run_steps _ _ _

private theorem nonexit_to_cycle (h : Steps sites n a b) (hb : b.control ≠ .exited) :
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

theorem cyclic_trace : CycleSteps exactSites 159 seed intermediate :=
  nonexit_to_cycle trace (by decide)

theorem halting_iff : CycleHalts exactSites seed ↔ CycleHalts exactSites intermediate :=
  cycle_prefix_halting_iff cyclic_trace (by decide)

#print axioms halting_iff
#print axioms trace
#print axioms cyclic_trace
#print axioms trace_checked
end M6.Source.SeedPrefix

