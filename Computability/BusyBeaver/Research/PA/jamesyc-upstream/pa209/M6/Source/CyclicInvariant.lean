module
public import M6.Source.CyclicDeterminism
@[expose] public section
namespace M6.Source

theorem CycleSteps.append (h₁ : CycleSteps sites n a b) (h₂ : CycleSteps sites m b c) :
    CycleSteps sites (n+m) a c := by
  induction h₁ with
  | refl => simpa only [Nat.zero_add] using h₂
  | cons h ih =>
    simpa only [Nat.succ_add] using CycleSteps.cons (ih h₂)

/-- A source invariant closed by positive finite macro segments excludes a
halt, provided its boundary states are not already halted. This explicit
condition matters because the source halt state is absorbing, not undefined. -/
theorem cycle_not_halts_of_positive_invariant
    (sites : Array Site) (Inv : Configuration → Prop)
    (nonhalt : ∀ c, Inv c → c.control ≠ .halted)
    (progress : ∀ c, Inv c → ∃ n d, 0 < n ∧ CycleSteps sites n c d ∧ Inv d)
    (c₀ : Configuration) (initial : Inv c₀) : ¬ CycleHalts sites c₀ := by
  intro hhalt
  obtain ⟨m,hm⟩ := hhalt
  have impossible : ∀ m c, Inv c → (cycleRun sites m c).control = .halted → False := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro c hc hm
      obtain ⟨n,d,hn,hstep,hd⟩ := progress c hc
      by_cases hnm : n ≤ m
      · have he : m = n+(m-n) := by omega
        rw [he,cycleRun_add,hstep.eq_run] at hm
        exact ih (m-n) (by omega) d hd hm
      · have he : n = m+(n-m) := by omega
        have hs : cycleStep sites (cycleRun sites m c) = cycleRun sites m c := by
          rcases hx : cycleRun sites m c with ⟨q,r⟩
          rw [hx] at hm
          simp only at hm
          subst q
          rfl
        have hr : cycleRun sites n c = cycleRun sites m c := by
          rw [he,cycleRun_add,cycleRun_stable hs]
        have hh : d.control = .halted := by rw [← hstep.eq_run,hr]; exact hm
        exact nonhalt d hd hh
  exact impossible m c₀ initial hm
#print axioms cycle_not_halts_of_positive_invariant
end M6.Source

