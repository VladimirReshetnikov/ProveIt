module
public import M6.Source.UnpairBinding
public import M6.Source.Semantics
public import M6.Source.Cantor
@[expose] public section

namespace M6.Source.Unpair

structure Store where
  w : Nat
  h : Nat
  x : Nat
  y : Nat
  frame : Registers

def registers (s : Store) : Registers := fun r =>
  if r = 2 then s.w else if r = 5 then s.h else if r = 6 then s.x else if r = 7 then s.y
  else s.frame r

def configAt (n : Nat) (s : Store) : Configuration := ⟨.at n, registers s⟩

def exitAt (s : Store) : Configuration := ⟨.exited, registers s⟩

@[simp] theorem read_w (s : Store) : registers s 2 = s.w := by simp [registers]
private theorem write_w (s : Store) (v : Nat) :
    write (registers s) 2 v = registers { s with w := v } := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write, registers]

@[simp] theorem read_h (s : Store) : registers s 5 = s.h := by simp [registers]
private theorem write_h (s : Store) (v : Nat) :
    write (registers s) 5 v = registers { s with h := v } := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write, registers]

@[simp] theorem read_x (s : Store) : registers s 6 = s.x := by simp [registers]
private theorem write_x (s : Store) (v : Nat) :
    write (registers s) 6 v = registers { s with x := v } := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write, registers]

@[simp] theorem read_y (s : Store) : registers s 7 = s.y := by simp [registers]
private theorem write_y (s : Store) (v : Nat) :
    write (registers s) 7 v = registers { s with y := v } := by
  funext r
  by_cases h2 : r = 2 <;> by_cases h5 : r = 5 <;> by_cases h6 : r = 6 <;> by_cases h7 : r = 7 <;>
    simp_all [write, registers]

private theorem step_3933 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3933 ⟨w, h, x, y, f⟩) = if w = 0 then configAt 3941 ⟨w, h, x, y, f⟩ else configAt 3934 ⟨w - 1, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 0), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨0, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  by_cases hz : w = 0
  all_goals simp_all [unpairExpected, execute, destination, configAt, write_w]

private theorem step_3934 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3934 ⟨w, h, x, y, f⟩) = configAt 3935 ⟨w, h, x, y + 1, f⟩ := by
  change step exactSites ⟨.at (3933 + 1), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨1, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt, write_y]

private theorem step_3935 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3935 ⟨w, h, x, y, f⟩) = if x = 0 then configAt 3937 ⟨w, h, x, y, f⟩ else configAt 3936 ⟨w, h, x - 1, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 2), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨2, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [unpairExpected, execute, destination, configAt, write_x]

private theorem step_3936 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3936 ⟨w, h, x, y, f⟩) = configAt 3940 ⟨w, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 3), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨3, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt]

private theorem step_3937 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3937 ⟨w, h, x, y, f⟩) = if y = 0 then configAt 3940 ⟨w, h, x, y, f⟩ else configAt 3938 ⟨w, h, x, y - 1, f⟩ := by
  change step exactSites ⟨.at (3933 + 4), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨4, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  by_cases hz : y = 0
  all_goals simp_all [unpairExpected, execute, destination, configAt, write_y]

private theorem step_3938 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3938 ⟨w, h, x, y, f⟩) = configAt 3939 ⟨w, h, x + 1, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 5), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨5, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt, write_x]

private theorem step_3939 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3939 ⟨w, h, x, y, f⟩) = configAt 3937 ⟨w, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 6), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨6, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt]

private theorem step_3940 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3940 ⟨w, h, x, y, f⟩) = configAt 3933 ⟨w, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 7), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨7, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt]

private theorem step_3941 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3941 ⟨w, h, x, y, f⟩) = if y = 0 then configAt 3944 ⟨w, h, x, y, f⟩ else configAt 3942 ⟨w, h, x, y - 1, f⟩ := by
  change step exactSites ⟨.at (3933 + 8), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨8, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  by_cases hz : y = 0
  all_goals simp_all [unpairExpected, execute, destination, configAt, write_y]

private theorem step_3942 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3942 ⟨w, h, x, y, f⟩) = configAt 3943 ⟨w + 1, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 9), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨9, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt, write_w]

private theorem step_3943 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3943 ⟨w, h, x, y, f⟩) = configAt 3941 ⟨w, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 10), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨10, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt]

private theorem step_3944 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3944 ⟨w, h, x, y, f⟩) = if x = 0 then exitAt ⟨w, h, x, y, f⟩ else configAt 3945 ⟨w, h, x - 1, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 11), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨11, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  by_cases hz : x = 0
  all_goals simp_all [unpairExpected, execute, destination, configAt, exitAt, write_x]

private theorem step_3945 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3945 ⟨w, h, x, y, f⟩) = configAt 3946 ⟨w, h + 1, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 12), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨12, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt, write_h]

private theorem step_3946 (w h x y : Nat) (f : Registers) :
    step exactSites (configAt 3946 ⟨w, h, x, y, f⟩) = configAt 3944 ⟨w, h, x, y, f⟩ := by
  change step exactSites ⟨.at (3933 + 13), registers ⟨w, h, x, y, f⟩⟩ = _
  rw [step_of_resolved (unpair_resolved_at ⟨13, by decide⟩) (registers ⟨w, h, x, y, f⟩)]
  simp_all [unpairExpected, execute, destination, configAt]

theorem steps_trans (ab : Steps sites n a b) (bc : Steps sites m b c) :
    Steps sites (n+m) a c := by
  induction ab with
  | refl => simpa using bc
  | cons h ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.cons (ih bc)

theorem move_y_x (y w h x : Nat) (f : Registers) :
    Steps exactSites (3*y+1) (configAt 3937 ⟨w, h, x, y, f⟩) (configAt 3940 ⟨w, h, x + y, 0, f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_3937]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_3937]
    try simp
    apply Steps.cons
    rw [step_3938]
    try simp
    apply Steps.cons
    rw [step_3939]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x+1)

theorem restore_y_w (y w h x : Nat) (f : Registers) :
    Steps exactSites (3*y+1) (configAt 3941 ⟨w, h, x, y, f⟩) (configAt 3944 ⟨w + y, h, x, 0, f⟩) := by
  induction y generalizing w with
  | zero =>
    apply Steps.cons
    rw [step_3941]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_3941]
    try simp
    apply Steps.cons
    rw [step_3942]
    try simp
    apply Steps.cons
    rw [step_3943]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (w+1)

theorem restore_x_h (x w h y : Nat) (f : Registers) :
    Steps exactSites (3*x+1) (configAt 3944 ⟨w, h, x, y, f⟩) (exitAt ⟨w, h + x, 0, y, f⟩) := by
  induction x generalizing h with
  | zero =>
    apply Steps.cons
    rw [step_3944]
    try simp
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+1 = (3*x+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_3944]
    try simp
    apply Steps.cons
    rw [step_3945]
    try simp
    apply Steps.cons
    rw [step_3946]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (h+1)

/-- Cost of one outer diagonal-enumeration round. -/
def roundCost (p : Nat × Nat) : Nat := if p.1 = 0 then 3*p.2+8 else 5

private theorem round_positive (a b w h : Nat) (f : Registers) :
    Steps exactSites 5
      (configAt 3933 ⟨w+1,h,a+1,b,f⟩) (configAt 3933 ⟨w,h,a,b+1,f⟩) := by
  apply Steps.cons
  rw [step_3933]
  try simp
  apply Steps.cons
  rw [step_3934]
  try simp
  apply Steps.cons
  rw [step_3935]
  try simp
  apply Steps.cons
  rw [step_3936]
  try simp
  apply Steps.cons
  rw [step_3940]
  try simp
  exact Steps.refl _

private theorem round_zero (b w h : Nat) (f : Registers) :
    Steps exactSites (3*b+8)
      (configAt 3933 ⟨w+1,h,0,b,f⟩) (configAt 3933 ⟨w,h,b+1,0,f⟩) := by
  have entrySegment : Steps exactSites 3
      (configAt 3933 ⟨w+1,h,0,b,f⟩) (configAt 3937 ⟨w,h,0,b+1,f⟩) := by
    apply Steps.cons
    rw [step_3933]
    try simp
    apply Steps.cons
    rw [step_3934]
    try simp
    apply Steps.cons
    rw [step_3935]
    try simp
    exact Steps.refl _
  have middle := move_y_x (b+1) w h 0 f
  simp only [Nat.zero_add] at middle
  have suffix : Steps exactSites 1
      (configAt 3940 ⟨w,h,b+1,0,f⟩) (configAt 3933 ⟨w,h,b+1,0,f⟩) := by
    apply Steps.cons
    rw [step_3940]
    exact Steps.refl _
  have q := steps_trans entrySegment (steps_trans middle suffix)
  have hn : 3*b+8 = 3+(3*(b+1)+1)+1 := by omega
  rw [hn]
  simpa [Nat.add_assoc] using q

theorem round (p : Nat × Nat) (w h : Nat) (f : Registers) :
    Steps exactSites (roundCost p)
      (configAt 3933 ⟨w+1,h,p.1,p.2,f⟩)
      (configAt 3933 ⟨w,h,(Cantor.advance p).1,(Cantor.advance p).2,f⟩) := by
  rcases p with ⟨a,b⟩
  cases a with
  | zero => simpa [roundCost, Cantor.advance] using round_zero b w h f
  | succ a => simpa [roundCost, Cantor.advance] using round_positive a b w h f

def loopCost : Nat → Nat × Nat → Nat
  | 0, _ => 1
  | n+1, p => roundCost p + loopCost n (Cantor.advance p)

/-- All-natural outer loop, measured by its decreasing W register. -/
theorem loop (n : Nat) (p : Nat × Nat) (h : Nat) (f : Registers) :
    Steps exactSites (loopCost n p)
      (configAt 3933 ⟨n,h,p.1,p.2,f⟩)
      (configAt 3941 ⟨0,h,(Cantor.decode (n+Cantor.pair p.1 p.2)).1,
        (Cantor.decode (n+Cantor.pair p.1 p.2)).2,f⟩) := by
  induction n generalizing p with
  | zero =>
    simp only [loopCost, Nat.zero_add, Cantor.decode_pair]
    apply Steps.cons
    rw [step_3933]
    try simp
    exact Steps.refl _
  | succ n ih =>
    have q := steps_trans (round p n h f) (ih (Cantor.advance p))
    have hn : n + Cantor.pair (Cantor.advance p).1 (Cantor.advance p).2 =
        n+1+Cantor.pair p.1 p.2 := by rw [Cantor.pair_advance]; omega
    simpa only [loopCost, hn] using q

/-- Exact literal stack unpairing. All unmentioned registers remain arbitrary. -/
theorem unpair (n : Nat) (f : Registers) :
    Steps exactSites
      (loopCost n (0,0) + (3*(Cantor.decode n).2+1) + (3*(Cantor.decode n).1+1))
      (configAt 3933 ⟨n,0,0,0,f⟩)
      (exitAt ⟨(Cantor.decode n).2,(Cantor.decode n).1,0,0,f⟩) := by
  have body := loop n (0,0) 0 f
  have yclean := restore_y_w (Cantor.decode n).2 0 0 (Cantor.decode n).1 f
  have xclean := restore_x_h (Cantor.decode n).1 (Cantor.decode n).2 0 0 f
  simp only [Cantor.pair, Cantor.triangle, Nat.add_zero] at body
  simp only [Nat.zero_add] at yclean xclean
  exact steps_trans (steps_trans body yclean) xclean

#print axioms unpair
end M6.Source.Unpair

