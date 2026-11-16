module
public import M6.Source.UnpairPartialSteps
@[expose] public section
namespace M6.Source.UnpairPartial
open Unpair (roundCost loopCost steps_trans)
variable {sites : Array Site} {base : Nat} (hbound : Bound sites base)
include hbound

theorem move_y_x (y w h x : Nat) (f : Registers) :
    Steps sites (3*y+1) (configAt base 3937 ⟨w, h, x, y, f⟩) (configAt base 3940 ⟨w, h, x + y, 0, f⟩) := by
  induction y generalizing x with
  | zero =>
    apply Steps.cons
    rw [step_3937 hbound]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_3937 hbound]
    try simp
    apply Steps.cons
    rw [step_3938 hbound]
    try simp
    apply Steps.cons
    rw [step_3939 hbound]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (x+1)

theorem restore_y_w (y w h x : Nat) (f : Registers) :
    Steps sites (3*y+1) (configAt base 3941 ⟨w, h, x, y, f⟩) (configAt base 3944 ⟨w + y, h, x, 0, f⟩) := by
  induction y generalizing w with
  | zero =>
    apply Steps.cons
    rw [step_3941 hbound]
    try simp
    exact Steps.refl _
  | succ y ih =>
    have hn : 3*(y+1)+1 = (3*y+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step_3941 hbound]
    try simp
    apply Steps.cons
    rw [step_3942 hbound]
    try simp
    apply Steps.cons
    rw [step_3943 hbound]
    try simp
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (w+1)

private theorem round_positive (a b w h : Nat) (f : Registers) :
    Steps sites 5
      (configAt base 3933 ⟨w+1,h,a+1,b,f⟩) (configAt base 3933 ⟨w,h,a,b+1,f⟩) := by
  apply Steps.cons
  rw [step_3933 hbound]
  try simp
  apply Steps.cons
  rw [step_3934 hbound]
  try simp
  apply Steps.cons
  rw [step_3935 hbound]
  try simp
  apply Steps.cons
  rw [step_3936 hbound]
  try simp
  apply Steps.cons
  rw [step_3940 hbound]
  try simp
  exact Steps.refl _

private theorem round_zero (b w h : Nat) (f : Registers) :
    Steps sites (3*b+8)
      (configAt base 3933 ⟨w+1,h,0,b,f⟩) (configAt base 3933 ⟨w,h,b+1,0,f⟩) := by
  have entrySegment : Steps sites 3
      (configAt base 3933 ⟨w+1,h,0,b,f⟩) (configAt base 3937 ⟨w,h,0,b+1,f⟩) := by
    apply Steps.cons
    rw [step_3933 hbound]
    try simp
    apply Steps.cons
    rw [step_3934 hbound]
    try simp
    apply Steps.cons
    rw [step_3935 hbound]
    try simp
    exact Steps.refl _
  have middle := move_y_x hbound (b+1) w h 0 f
  simp only [Nat.zero_add] at middle
  have suffix : Steps sites 1
      (configAt base 3940 ⟨w,h,b+1,0,f⟩) (configAt base 3933 ⟨w,h,b+1,0,f⟩) := by
    apply Steps.cons
    rw [step_3940 hbound]
    exact Steps.refl _
  have q := steps_trans entrySegment (steps_trans middle suffix)
  have hn : 3*b+8 = 3+(3*(b+1)+1)+1 := by omega
  rw [hn]
  simpa [Nat.add_assoc] using q

theorem round (p : Nat × Nat) (w h : Nat) (f : Registers) :
    Steps sites (roundCost p)
      (configAt base 3933 ⟨w+1,h,p.1,p.2,f⟩)
      (configAt base 3933 ⟨w,h,(Cantor.advance p).1,(Cantor.advance p).2,f⟩) := by
  rcases p with ⟨a,b⟩
  cases a with
  | zero => simpa [roundCost, Cantor.advance] using round_zero hbound b w h f
  | succ a => simpa [roundCost, Cantor.advance] using round_positive hbound a b w h f

theorem loop (n : Nat) (p : Nat × Nat) (h : Nat) (f : Registers) :
    Steps sites (loopCost n p)
      (configAt base 3933 ⟨n,h,p.1,p.2,f⟩)
      (configAt base 3941 ⟨0,h,(Cantor.decode (n+Cantor.pair p.1 p.2)).1,
        (Cantor.decode (n+Cantor.pair p.1 p.2)).2,f⟩) := by
  induction n generalizing p with
  | zero =>
    simp only [loopCost, Nat.zero_add, Cantor.decode_pair]
    apply Steps.cons
    rw [step_3933 hbound]
    try simp
    exact Steps.refl _
  | succ n ih =>
    have q := steps_trans (round hbound p n h f) (ih (Cantor.advance p))
    have hn : n + Cantor.pair (Cantor.advance p).1 (Cantor.advance p).2 =
        n+1+Cantor.pair p.1 p.2 := by rw [Cantor.pair_advance]; omega
    simpa only [loopCost, hn] using q


/-- Partial decoder stops before the head-restoration tail. It leaves the
head in X for arithmetic consumers, without asserting an absorbing exit. -/
theorem decode_prefix (n h : Nat) (f : Registers) :
    Steps sites (loopCost n (0,0)+(3*(Cantor.decode n).2+1))
      (configAt base 3933 ⟨n,h,0,0,f⟩)
      (configAt base 3944 ⟨(Cantor.decode n).2,h,(Cantor.decode n).1,0,f⟩) := by
  have a : Steps sites (loopCost n (0,0))
      (configAt base 3933 ⟨n,h,0,0,f⟩)
      (configAt base 3941 ⟨0,h,(Cantor.decode n).1,(Cantor.decode n).2,f⟩) := by
    simpa only [Cantor.pair,Cantor.triangle,Nat.add_zero] using loop hbound n (0,0) h f
  have b := restore_y_w hbound (Cantor.decode n).2 0 h (Cantor.decode n).1 f
  simpa only [Nat.zero_add] using steps_trans a b

omit hbound in
theorem original_bound : Bound exactSites 3933 := by
  intro ⟨j,hj⟩
  have hc : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact unpair_resolved_at ⟨0,by decide⟩
  · exact unpair_resolved_at ⟨1,by decide⟩
  · exact unpair_resolved_at ⟨2,by decide⟩
  · exact unpair_resolved_at ⟨3,by decide⟩
  · exact unpair_resolved_at ⟨4,by decide⟩
  · exact unpair_resolved_at ⟨5,by decide⟩
  · exact unpair_resolved_at ⟨6,by decide⟩
  · exact unpair_resolved_at ⟨7,by decide⟩
  · exact unpair_resolved_at ⟨8,by decide⟩
  · exact unpair_resolved_at ⟨9,by decide⟩
  · exact unpair_resolved_at ⟨10,by decide⟩

#print axioms decode_prefix
end M6.Source.UnpairPartial

