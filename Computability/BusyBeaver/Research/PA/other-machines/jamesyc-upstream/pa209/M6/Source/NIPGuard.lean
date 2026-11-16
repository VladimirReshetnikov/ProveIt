module
public import M6.Source.NIPBinding
public import M6.Source.S36Lift
@[expose] public section

namespace M6.Source.NIPGuard

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

private theorem step_3921 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3921 ⟨t, h, x, f⟩) = configAt 3922 ⟨t, h, x + 1, f⟩ := by
  change step exactSites ⟨.at (3921 + 0), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨0, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_3922 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3922 ⟨t, h, x, f⟩) = if h = 0 then configAt 3926 ⟨t, h, x, f⟩ else configAt 3923 ⟨t, h - 1, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 1), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨1, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : h = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_h]

private theorem step_3923 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3923 ⟨t, h, x, f⟩) = if x = 0 then configAt 3925 ⟨t, h, x, f⟩ else configAt 3924 ⟨t, h, x - 1, f⟩ := by
  change step exactSites ⟨.at (3921 + 2), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨2, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_3924 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3924 ⟨t, h, x, f⟩) = configAt 3922 ⟨t, h, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 3), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨3, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_3925 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3925 ⟨t, h, x, f⟩) = configAt 3927 ⟨t, h, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 4), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨4, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_3926 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3926 ⟨t, h, x, f⟩) = if x = 0 then configAt 3932 ⟨t, h, x, f⟩ else configAt 3927 ⟨t, h, x - 1, f⟩ := by
  change step exactSites ⟨.at (3921 + 5), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨5, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_3927 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3927 ⟨t, h, x, f⟩) = if h = 0 then configAt 3929 ⟨t, h, x, f⟩ else configAt 3928 ⟨t, h - 1, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 6), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨6, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : h = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_h]

private theorem step_3928 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3928 ⟨t, h, x, f⟩) = configAt 3927 ⟨t, h, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 7), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨7, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_3929 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3929 ⟨t, h, x, f⟩) = if x = 0 then configAt 3931 ⟨t, h, x, f⟩ else configAt 3930 ⟨t, h, x - 1, f⟩ := by
  change step exactSites ⟨.at (3921 + 8), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨8, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [nipExpected, execute, destination, configAt, write_x]

private theorem step_3930 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3930 ⟨t, h, x, f⟩) = configAt 3927 ⟨t, h, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 9), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨9, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_3931 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3931 ⟨t, h, x, f⟩) = configAt 3933 ⟨t, h, x, f⟩ := by
  change step exactSites ⟨.at (3921 + 10), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨10, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute, destination, configAt]

private theorem step_3932 (t h x : Nat) (f : Registers) :
    step exactSites (configAt 3932 ⟨t, h, x, f⟩) = ⟨.halted, S36Lift.registers ⟨t, h, x, f⟩⟩ := by
  change step exactSites ⟨.at (3921 + 11), S36Lift.registers ⟨t, h, x, f⟩⟩ = _
  rw [step_of_resolved (nip_resolved_at ⟨11, by decide⟩) (S36Lift.registers ⟨t, h, x, f⟩)]
  simp_all [nipExpected, execute]

/-- The cleanup branch consumes H, keeping every other register unchanged. -/
theorem clear_h (h t : Nat) (f : Registers) :
    Steps exactSites (2*h + 3) (configAt 3927 ⟨t,h,0,f⟩) (configAt 3933 ⟨t,0,0,f⟩) := by
  induction h with
  | zero =>
    apply Steps.cons
    rw [step_3927]
    try simp
    apply Steps.cons
    rw [step_3929]
    try simp
    apply Steps.cons
    rw [step_3931]
    exact Steps.refl _
  | succ h ih =>
    have hn : 2*(h+1)+3 = (2*h+3)+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_3927]
    try simp
    apply Steps.cons
    rw [step_3928]
    exact ih

theorem guard_zero (t : Nat) (f : Registers) :
    Steps exactSites 6 (configAt 3921 ⟨t,0,0,f⟩) (configAt 3933 ⟨t,0,0,f⟩) := by
  apply Steps.cons
  rw [step_3921]
  try simp
  apply Steps.cons
  rw [step_3922]
  try simp
  apply Steps.cons
  rw [step_3926]
  try simp
  apply Steps.cons
  rw [step_3927]
  try simp
  apply Steps.cons
  rw [step_3929]
  try simp
  apply Steps.cons
  rw [step_3931]
  try simp
  exact Steps.refl _

theorem guard_one (t : Nat) (f : Registers) :
    Steps exactSites 7 (configAt 3921 ⟨t,1,0,f⟩) (⟨.halted, S36Lift.registers ⟨t,0,0,f⟩⟩) := by
  apply Steps.cons
  rw [step_3921]
  try simp
  apply Steps.cons
  rw [step_3922]
  try simp
  apply Steps.cons
  rw [step_3923]
  try simp
  apply Steps.cons
  rw [step_3924]
  try simp
  apply Steps.cons
  rw [step_3922]
  try simp
  apply Steps.cons
  rw [step_3926]
  try simp
  apply Steps.cons
  rw [step_3932]
  try simp
  exact Steps.refl _

theorem guard_ge_two (h t : Nat) (f : Registers) :
    Steps exactSites (2*(h+2)+6) (configAt 3921 ⟨t,h+2,0,f⟩) (configAt 3933 ⟨t,0,0,f⟩) := by
  have hn : 2*(h+2)+6 = (2*h+3)+1+1+1+1+1+1+1 := by omega
  rw [hn]
  apply Steps.cons
  rw [step_3921]
  try simp
  apply Steps.cons
  rw [step_3922]
  try simp
  apply Steps.cons
  rw [step_3923]
  try simp
  apply Steps.cons
  rw [step_3924]
  try simp
  apply Steps.cons
  rw [step_3922]
  try simp
  apply Steps.cons
  rw [step_3923]
  try simp
  apply Steps.cons
  rw [step_3925]
  try simp
  exact clear_h h t f

/-- Every non-one guard value reaches stack decoding, clearing H and X. -/
theorem guard_not_one (h t : Nat) (f : Registers) (hne : h ≠ 1) :
    Steps exactSites (2*h+6) (configAt 3921 ⟨t,h,0,f⟩) (configAt 3933 ⟨t,0,0,f⟩) := by
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
    Steps exactSites (6*t + 7*h + 10)
      (configAt 3911 ⟨t,h,0,f⟩) ⟨.halted, S36Lift.registers ⟨h,0,0,f⟩⟩ := by
  have before := S36Lift.exact_pre_guard t h f
  have after := guard_one h f
  have bridge : S36Lift.embed ⟨10, ⟨h,t+h,0,f⟩⟩ = configAt 3921 ⟨h,1,0,f⟩ := by
    simp [S36Lift.embed, configAt, hs]
  rw [bridge] at before
  have q := steps_trans before after
  have hn : 6*t + 7*h + 10 = (6*t + 7*h + 3) + 7 := by omega
  rw [hn]
  exact q

/-- The nonhalting guard branch reaches stack decoding. This does not assert
that later source execution cannot halt. -/
theorem s36_reaches_stack_of_sum_ne_one (t h : Nat) (f : Registers) (hs : t+h ≠ 1) :
    Steps exactSites (8*t + 9*h + 9)
      (configAt 3911 ⟨t,h,0,f⟩) (configAt 3933 ⟨h,0,0,f⟩) := by
  have before := S36Lift.exact_pre_guard t h f
  have after := guard_not_one (t+h) h f hs
  have q := steps_trans before after
  have hn : 8*t + 9*h + 9 = (6*t + 7*h + 3) + (2*(t+h)+6) := by omega
  rw [hn]
  exact q

#print axioms s36_halts_of_sum_one
#print axioms s36_reaches_stack_of_sum_ne_one

end M6.Source.NIPGuard

