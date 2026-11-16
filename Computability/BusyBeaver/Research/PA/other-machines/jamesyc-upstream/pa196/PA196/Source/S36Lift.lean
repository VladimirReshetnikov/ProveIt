module
public import PA196.Source.S36Binding
public import M6.Source.Semantics
/-! Arithmetic proof adapted from M6.Source.S36Lift; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section

namespace PA196.Source.S36Lift
open M6.Source

abbrev LocalStore := S36Drain.Store Registers
abbrev LocalConfig := S36Drain.Config Registers

def registers (s : LocalStore) : Registers := fun r =>
  if r = 1 then s.t else if r = 5 then s.h else if r = 6 then s.x else s.frame r

def embed (c : LocalConfig) : Configuration :=
  ⟨.at (3800 + c.pc), registers c.store⟩

private theorem pc_cases {pc : Nat} (h : pc < 10) :
    pc = 0 ∨ pc = 1 ∨ pc = 2 ∨ pc = 3 ∨ pc = 4 ∨
    pc = 5 ∨ pc = 6 ∨ pc = 7 ∨ pc = 8 ∨ pc = 9 := by omega

private theorem write_t (s : LocalStore) (v : Nat) :
    write (registers s) 1 v = registers { s with t := v } := by
  funext r
  by_cases h1 : r = 1 <;> simp [write, registers, h1]

private theorem write_h (s : LocalStore) (v : Nat) :
    write (registers s) 5 v = registers { s with h := v } := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;>
    simp_all [write, registers]

private theorem write_x (s : LocalStore) (v : Nat) :
    write (registers s) 6 v = registers { s with x := v } := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [write, registers]

@[simp] theorem registers_t (s : LocalStore) : registers s 1 = s.t := by simp [registers]
@[simp] theorem registers_h (s : LocalStore) : registers s 5 = s.h := by simp [registers]
@[simp] theorem registers_x (s : LocalStore) : registers s 6 = s.x := by simp [registers]

/-- Every primitive transition of the local fragment is an actual transition
of the literal full source, for arbitrary values of all nine registers. -/
theorem step_commutes (c : LocalConfig) (hpc : c.pc < 10) :
    step Program.sites (embed c) = embed (S36Drain.step c) := by
  rcases c with ⟨pc, s⟩
  rcases pc_cases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change step Program.sites ⟨.at (3800 + 0), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨0, by decide⟩) (registers s)]
    by_cases hz : s.t = 0
    all_goals simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_t]
  · change step Program.sites ⟨.at (3800 + 1), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨1, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_x]
  · change step Program.sites ⟨.at (3800 + 2), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨2, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed]
  · change step Program.sites ⟨.at (3800 + 3), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨3, by decide⟩) (registers s)]
    by_cases hz : s.h = 0
    all_goals simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_h]
  · change step Program.sites ⟨.at (3800 + 4), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨4, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_t]
  · change step Program.sites ⟨.at (3800 + 5), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨5, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_x]
  · change step Program.sites ⟨.at (3800 + 6), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨6, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed]
  · change step Program.sites ⟨.at (3800 + 7), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨7, by decide⟩) (registers s)]
    by_cases hz : s.x = 0
    all_goals simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_x]
  · change step Program.sites ⟨.at (3800 + 8), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨8, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed, write_h]
  · change step Program.sites ⟨.at (3800 + 9), registers s⟩ = _
    rw [step_of_resolved (s36_resolved_at ⟨9, by decide⟩) (registers s)]
    simp_all [s36Expected, execute, destination, S36Drain.step, embed]

/-- Remaining fragment duration. Unlike the full source step, the local step
stutters at its exit. This potential prevents transporting such extra stutters. -/
def fuel (c : LocalConfig) : Nat :=
  let t := c.store.t; let h := c.store.h; let x := c.store.x
  match c.pc with
  | 0 => 6*t + 7*h + 3*x + 3
  | 1 => 6*t + 7*h + 3*x + 8
  | 2 => 6*t + 7*h + 3*x + 4
  | 3 => 7*h + 3*x + 2
  | 4 => 7*h + 3*x + 8
  | 5 => 7*h + 3*x + 7
  | 6 => 7*h + 3*x + 3
  | 7 => 3*x + 1
  | 8 => 3*x + 3
  | 9 => 3*x + 2
  | _ => 0

private theorem exit_fuel (c : LocalConfig) (hp : c.pc ≤ 10) (hf : 0 < fuel c) :
    c.pc < 10 := by
  by_cases h : c.pc < 10
  · exact h
  · have he : c.pc = 10 := by omega
    simp [fuel, he] at hf

private theorem step_pc (c : LocalConfig) (hp : c.pc < 10) :
    (S36Drain.step c).pc ≤ 10 := by
  rcases c with ⟨pc, s⟩
  rcases pc_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (by_cases ht : s.t = 0) <;> (by_cases hh : s.h = 0) <;> (by_cases hx : s.x = 0) <;>
    simp [S36Drain.step, ht, hh, hx]

private theorem fuel_step (c : LocalConfig) (hp : c.pc < 10) :
    fuel c = fuel (S36Drain.step c) + 1 := by
  rcases c with ⟨pc, s⟩
  rcases pc_cases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (by_cases ht : s.t = 0) <;> (by_cases hh : s.h = 0) <;> (by_cases hx : s.x = 0) <;>
    simp [S36Drain.step, fuel, ht, hh, hx] <;> omega

/-- Transport only steps before the local exit, whose full-source successor
must not be confused with the local absorbing convention. -/
theorem lift_steps (h : S36Drain.Steps n a b) (hp : a.pc ≤ 10) (hn : n ≤ fuel a) :
    Steps Program.sites n (embed a) (embed b) := by
  induction h with
  | refl => exact Steps.refl _
  | @cons n a b h ih =>
    have ha : a.pc < 10 := exit_fuel a hp (by omega)
    have hf := fuel_step a ha
    have q := ih (step_pc a ha) (by omega)
    rw [← step_commutes a ha] at q
    exact Steps.cons q

/-- The exact source ordinals 3800–3809 perform the proved S36 drain, including
all unchanged registers, and reach the actual NIP entry at ordinal 3810. -/
theorem exact_pre_guard (t h : Nat) (f : Registers) :
    Steps Program.sites (6*t + 7*h + 3)
      (embed ⟨0, ⟨t, h, 0, f⟩⟩) (embed ⟨10, ⟨h, t+h, 0, f⟩⟩) := by
  apply lift_steps (S36Drain.pre_guard t h f)
  · simp
  · simp [fuel]

#print axioms exact_pre_guard
end PA196.Source.S36Lift

