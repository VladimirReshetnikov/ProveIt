module
public import M6.Source.ActualCommandDiscard
@[expose] public section
namespace M6.Source.ActualCommandMacros
open Cantor Enumeration ActualAXCode
open AXCode (wim wal)

/-- Repeated literal H blocks; no new primitive instruction. -/
def popHeads : Nat → List Command
  | 0 => []
  | n+1 => H ++ popHeads n

theorem popHeads_zero (s : CommandStore) : commandsEval (popHeads 0) s = some s := rfl

theorem popHeads_succ (n t x w d h : Nat) :
    commandsEval (popHeads (n+1)) ⟨t,pair x w,d,h⟩ =
      commandsEval (popHeads n) ⟨t,w,0,x⟩ := by
  rw [popHeads,commandsEval_append,H_total]
  rfl

theorem popHeads_stack (xs : List Nat) (t x w d h : Nat) :
    commandsEval (popHeads (xs.length+1))
      ⟨t,(xs ++ [x]).foldr pair w,d,h⟩ = some ⟨t,w,0,x⟩ := by
  induction xs generalizing d h with
  | nil => simpa only [List.nil_append,List.foldr_cons,List.foldr_nil,List.length_nil,popHeads_zero] using
      popHeads_succ 0 t x w d h
  | cons y ys ih =>
      simp only [List.length_cons,List.cons_append,List.foldr_cons]
      rw [popHeads_succ]
      exact ih 0 y

theorem commandsEval_singleton (c : Command) (s : CommandStore) :
    commandsEval [c] s = commandEval c s := by
  simp only [commandsEval]
  cases commandEval c s <;> rfl

theorem append_total {xs ys : List Command} {s m out : CommandStore}
    (hx : commandsEval xs s = some m) (hy : commandsEval ys m = some out) :
    commandsEval (xs++ys) s = some out := by
  rw [commandsEval_append,hx]
  exact hy

def gateWord (a b c : Nat) : List Command := DISCARD ++ [.ax c a b] ++ popHeads 10

/-- The exact raw gate selector preserves the incoming encoded stack. -/
theorem gateWord_total (a b c t w : Nat) :
    commandsEval (gateWord a b c) ⟨t,w,0,0⟩ =
      some ⟨gate a b c,w,0,0⟩ := by
  unfold gateWord
  refine @append_total (DISCARD ++ [Command.ax c a b]) (popHeads 10)
    ⟨t,w,0,0⟩ ⟨gate a b c,(pa135Heads a b c 0 0 ++ [0]).foldr pair w,0,0⟩
    ⟨gate a b c,w,0,0⟩ ?_ ?_
  · apply append_total (DISCARD_total t w)
    rw [commandsEval_singleton]
    simpa only [Nat.zero_add] using ax_step c a b ⟨0,w,0,0⟩
  · exact popHeads_stack (pa135Heads a b c 0 0) (gate a b c) 0 w 0 0

#print axioms popHeads_succ
#print axioms popHeads_stack
#print axioms gateWord_total
end M6.Source.ActualCommandMacros

