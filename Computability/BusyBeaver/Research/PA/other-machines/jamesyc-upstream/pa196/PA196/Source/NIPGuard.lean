module
public import PA196.Source.NIPBinding
public import PA196.Source.S36Lift
/-! Arithmetic proof adapted from M6.Source.NIPGuard; every literal
source binding is reproved against the PA196 program. -/
@[expose] public section

namespace PA196.Source.NIPGuard
open M6.Source

abbrev Store := S36Lift.LocalStore

def configAt (n : Nat) (s : Store) : Configuration := ⟨.at n, S36Lift.registers s⟩

private theorem write_h (s : Store) (v : Nat) :
    write (S36Lift.registers s) 5 v = S36Lift.registers { s with h := v } := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;>
    simp_all [write, S36Lift.registers]

private theorem write_x (s : Store) (v : Nat) :
    write (S36Lift.registers s) 6 v = S36Lift.registers { s with x := v } := by
  funext r
  by_cases h1 : r = 1 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;>
    simp_all [write, S36Lift.registers]

private theorem step_3810 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 3810 ⟨t, h, x, f⟩) = configAt 3811 ⟨t, h, x + 1, f⟩ := by
  change step Program.sites ⟨.at 3810, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 3810 = some nipExpected[0] :=
    nip_resolved_at ⟨0,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_extra (s : Store) :
    step Program.sites (configAt 3811 s) = configAt 0 s := by
  have h : resolveAt Program.sites 3811 = some (.jump (some 0)) := by
    rw [Program.resolve_tree]
    decide +kernel
  rw [configAt,step_of_resolved h]
  rfl

private theorem step_0 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 0 ⟨t, h, x, f⟩) = if h = 0 then configAt 4 ⟨t, h, x, f⟩ else configAt 1 ⟨t, h - 1, x, f⟩ := by
  change step Program.sites ⟨.at 0, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 0 = some nipExpected[1] :=
    nip_resolved_at ⟨1,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : h = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_h]

private theorem step_1 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 1 ⟨t, h, x, f⟩) = if x = 0 then configAt 3 ⟨t, h, x, f⟩ else configAt 2 ⟨t, h, x - 1, f⟩ := by
  change step Program.sites ⟨.at 1, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 1 = some nipExpected[2] :=
    nip_resolved_at ⟨2,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_2 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 2 ⟨t, h, x, f⟩) = configAt 0 ⟨t, h, x, f⟩ := by
  change step Program.sites ⟨.at 2, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 2 = some nipExpected[3] :=
    nip_resolved_at ⟨3,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_3 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 3 ⟨t, h, x, f⟩) = configAt 5 ⟨t, h, x, f⟩ := by
  change step Program.sites ⟨.at 3, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 3 = some nipExpected[4] :=
    nip_resolved_at ⟨4,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_4 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 4 ⟨t, h, x, f⟩) = if x = 0 then configAt 10 ⟨t, h, x, f⟩ else configAt 5 ⟨t, h, x - 1, f⟩ := by
  change step Program.sites ⟨.at 4, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 4 = some nipExpected[5] :=
    nip_resolved_at ⟨5,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_5 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 5 ⟨t, h, x, f⟩) = if h = 0 then configAt 7 ⟨t, h, x, f⟩ else configAt 6 ⟨t, h - 1, x, f⟩ := by
  change step Program.sites ⟨.at 5, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 5 = some nipExpected[6] :=
    nip_resolved_at ⟨6,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : h = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_h]

private theorem step_6 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 6 ⟨t, h, x, f⟩) = configAt 5 ⟨t, h, x, f⟩ := by
  change step Program.sites ⟨.at 6, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 6 = some nipExpected[7] :=
    nip_resolved_at ⟨7,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_7 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 7 ⟨t, h, x, f⟩) = if x = 0 then configAt 9 ⟨t, h, x, f⟩ else configAt 8 ⟨t, h, x - 1, f⟩ := by
  change step Program.sites ⟨.at 7, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 7 = some nipExpected[8] :=
    nip_resolved_at ⟨8,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_8 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 8 ⟨t, h, x, f⟩) = configAt 5 ⟨t, h, x, f⟩ := by
  change step Program.sites ⟨.at 8, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 8 = some nipExpected[9] :=
    nip_resolved_at ⟨9,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_9 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 9 ⟨t, h, x, f⟩) = configAt 11 ⟨t, h, x, f⟩ := by
  change step Program.sites ⟨.at 9, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 9 = some nipExpected[10] :=
    nip_resolved_at ⟨10,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_10 (t h x : Nat) (f : Registers) :
    step Program.sites (configAt 10 ⟨t, h, x, f⟩) = ⟨.halted, S36Lift.registers ⟨t, h, x, f⟩⟩ := by
  change step Program.sites ⟨.at 10, S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  have hb : resolveAt Program.sites 10 = some nipExpected[11] :=
    nip_resolved_at ⟨11,by decide⟩
  rw [step_of_resolved hb (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute]

/-- The cleanup branch consumes H, keeping every other register unchanged. -/
theorem clear_h (h t : Nat) (f : Registers) :
    Steps Program.sites (2*h + 3) (configAt 5 ⟨t,h,0,f⟩) (configAt 11 ⟨t,0,0,f⟩) := by
  induction h with
  | zero =>
    apply Steps.cons
    rw [step_5]
    try simp
    apply Steps.cons
    rw [step_7]
    try simp
    apply Steps.cons
    rw [step_9]
    exact Steps.refl _
  | succ h ih =>
    have hn : 2*(h+1)+3 = (2*h+3)+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_5]
    try simp
    apply Steps.cons
    rw [step_6]
    exact ih

theorem guard_zero (t : Nat) (f : Registers) :
    Steps Program.sites 7 (configAt 3810 ⟨t,0,0,f⟩) (configAt 11 ⟨t,0,0,f⟩) := by
  apply Steps.cons
  rw [step_3810]
  apply Steps.cons
  rw [step_extra]
  try simp
  apply Steps.cons
  rw [step_0]
  try simp
  apply Steps.cons
  rw [step_4]
  try simp
  apply Steps.cons
  rw [step_5]
  try simp
  apply Steps.cons
  rw [step_7]
  try simp
  apply Steps.cons
  rw [step_9]
  try simp
  exact Steps.refl _

theorem guard_one (t : Nat) (f : Registers) :
    Steps Program.sites 8 (configAt 3810 ⟨t,1,0,f⟩) (⟨.halted, S36Lift.registers ⟨t,0,0,f⟩⟩) := by
  apply Steps.cons
  rw [step_3810]
  apply Steps.cons
  rw [step_extra]
  try simp
  apply Steps.cons
  rw [step_0]
  try simp
  apply Steps.cons
  rw [step_1]
  try simp
  apply Steps.cons
  rw [step_2]
  try simp
  apply Steps.cons
  rw [step_0]
  try simp
  apply Steps.cons
  rw [step_4]
  try simp
  apply Steps.cons
  rw [step_10]
  try simp
  exact Steps.refl _

theorem guard_ge_two (h t : Nat) (f : Registers) :
    Steps Program.sites (2*(h+2)+7) (configAt 3810 ⟨t,h+2,0,f⟩) (configAt 11 ⟨t,0,0,f⟩) := by
  have hn : 2*(h+2)+7 = (2*h+3)+1+1+1+1+1+1+1+1 := by omega
  rw [hn]
  apply Steps.cons
  rw [step_3810]
  apply Steps.cons
  rw [step_extra]
  try simp
  apply Steps.cons
  rw [step_0]
  try simp
  apply Steps.cons
  rw [step_1]
  try simp
  apply Steps.cons
  rw [step_2]
  try simp
  apply Steps.cons
  rw [step_0]
  try simp
  apply Steps.cons
  rw [step_1]
  try simp
  apply Steps.cons
  rw [step_3]
  try simp
  exact clear_h h t f

/-- Every non-one guard value reaches stack decoding, clearing H and X. -/
theorem guard_not_one (h t : Nat) (f : Registers) (hne : h ≠ 1) :
    Steps Program.sites (2*h+7) (configAt 3810 ⟨t,h,0,f⟩) (configAt 11 ⟨t,0,0,f⟩) := by
  cases h with
  | zero => exact guard_zero t f
  | succ h => cases h with
    | zero => exact False.elim (hne rfl)
    | succ h => exact guard_ge_two h t f

private theorem steps_trans (ab : Steps sites n a b) (bc : Steps sites m b c) :
    Steps sites (n + m) a c := by
  induction ab with
  | refl => simpa using bc
  | cons h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons (ih bc)

/-- Exact source S36 halting branch, not an assumed macro contract. -/
theorem s36_halts_of_sum_one (t h : Nat) (f : Registers) (hs : t+h = 1) :
    Steps Program.sites (6*t + 7*h + 11)
      (configAt 3800 ⟨t,h,0,f⟩) ⟨.halted, S36Lift.registers ⟨h,0,0,f⟩⟩ := by
  have before := S36Lift.exact_pre_guard t h f
  have after := guard_one h f
  have bridge : S36Lift.embed ⟨10, ⟨h,t+h,0,f⟩⟩ = configAt 3810 ⟨h,1,0,f⟩ := by
    simp [S36Lift.embed, configAt, hs]
  rw [bridge] at before
  have q := steps_trans before after
  have hn : 6*t + 7*h + 11 = (6*t + 7*h + 3) + 8 := by omega
  rw [hn]
  exact q

/-- The nonhalting guard branch reaches stack decoding. This does not assert
that later source execution cannot halt. -/
theorem s36_reaches_stack_of_sum_ne_one (t h : Nat) (f : Registers) (hs : t+h ≠ 1) :
    Steps Program.sites (8*t + 9*h + 10)
      (configAt 3800 ⟨t,h,0,f⟩) (configAt 11 ⟨h,0,0,f⟩) := by
  have before := S36Lift.exact_pre_guard t h f
  have after := guard_not_one (t+h) h f hs
  have q := steps_trans before after
  have hn : 8*t + 9*h + 10 = (6*t + 7*h + 3) + (2*(t+h)+7) := by omega
  rw [hn]
  exact q

#print axioms s36_halts_of_sum_one
#print axioms s36_reaches_stack_of_sum_ne_one

end PA196.Source.NIPGuard

