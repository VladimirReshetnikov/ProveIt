module
public import PA196.Commands.Code
@[expose] public section

/-! The paper's arithmetic command interpreter. `none` means the Shift halt
test succeeded; it never means a failed or undefined arithmetic operation. -/
namespace PA196.Commands
open M6.Source.Cantor

inductive Command where
  | shift
  | mp (offset : Nat)
  | ax (c x y : Nat)
  deriving DecidableEq, Repr

structure Store where
  t : Nat
  w : Nat
  d : Nat
  h : Nat
  deriving DecidableEq, Repr

def step : Command → Store → Option Store
  | .shift, s =>
      if s.t + s.h = 1 then none
      else some ⟨s.h, (decode s.w).2, s.d, (decode s.w).1⟩
  | .mp x, s =>
      let y := s.d + x
      if Code.I s.t y = s.h then some ⟨y, pair 0 s.w, y, 0⟩
      else some ⟨0, s.w, y, 0⟩
  | .ax c x y, s =>
      some ⟨Code.gate (s.h + y) (s.d + x) c,
        (Code.heads (s.d + x) (s.h + y) c s.d s.h ++ [s.t]).foldr pair s.w, 0, 0⟩

def run : List Command → Store → Option Store
  | [], s => some s
  | c :: cs, s => (step c s).bind (run cs)

theorem run_append (xs ys : List Command) (s : Store) :
    run (xs ++ ys) s = (run xs s).bind (run ys) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, run]
    cases h : step x s <;> simp [ih]

theorem append_total {xs ys : List Command} {s m e : Store}
    (hx : run xs s = some m) (hy : run ys m = some e) :
    run (xs ++ ys) s = some e := by
  rw [run_append, hx]
  exact hy

theorem append_none {xs ys : List Command} {s : Store}
    (h : run xs s = none) : run (xs ++ ys) s = none := by
  rw [run_append, h]
  rfl

theorem append_some_none {xs ys : List Command} {s m : Store}
    (hx : run xs s = some m) (hy : run ys m = none) :
    run (xs ++ ys) s = none := by
  rw [run_append, hx]
  exact hy

theorem ax_step (c x y : Nat) (s : Store) :
    step (.ax c x y) s = some ⟨Code.gate (s.h + y) (s.d + x) c,
      (Code.heads (s.d + x) (s.h + y) c s.d s.h ++ [s.t]).foldr pair s.w, 0, 0⟩ := rfl

theorem shift_pair (t h x w d : Nat) (hs : t + h ≠ 1) :
    step .shift ⟨t, pair x w, d, h⟩ = some ⟨h, w, d, x⟩ := by
  simp [step, hs, decode_pair]

theorem shift_halts (s : Store) (h : s.t + s.h = 1) : step .shift s = none := by
  simp [step, h]

#print axioms run_append
end PA196.Commands
