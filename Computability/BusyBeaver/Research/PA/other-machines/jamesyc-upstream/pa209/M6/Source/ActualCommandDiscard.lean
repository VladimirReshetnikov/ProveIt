module
public import M6.Source.ActualCommandMacros
@[expose] public section

/-! DISCARD is proved with a symbolic positive selector before specializing
to1. This avoids kernel normalization of enormous closed nested axiom codes;
the proof still uses the exact arithmetic command interpreter and AX frame. -/
namespace M6.Source.ActualCommandMacros
open Cantor Enumeration
open AXCode (wim wal)

def discardWith (c : Nat) : List Command :=
  [.mp c,.ax c 0 0] ++ List.replicate 10 .shift ++ [.mp 0]

theorem discardWith_total (c : Nat) (hc : 0 < c) (t w : Nat) :
    commandsEval (discardWith c) ⟨t,w,0,0⟩ = some ⟨0,w,0,0⟩ := by
  have hp := M6.Source.Enumeration.pair_bounds t c
  have he : wim t c ≠ 0 := by simp only [wim,implication]; omega
  have hfirst : commandsEval [.mp c] ⟨t,w,0,0⟩ = some ⟨0,w,c,0⟩ := by simp [commandsEval,commandEval,he]
  change commandsEval ([.mp c] ++ ([.ax c 0 0] ++ List.replicate 10 .shift) ++ [.mp 0]) ⟨t,w,0,0⟩ = _
  rw [commandsEval_append,commandsEval_append,hfirst]
  simp only [Option.bind_some,AX_shift10]
  simp [commandsEval,commandEval]

theorem DISCARD_total (t w : Nat) : commandsEval DISCARD ⟨t,w,0,0⟩ = some ⟨0,w,0,0⟩ := by
  simpa only [discardWith,DISCARD] using discardWith_total 1 (by decide) t w

#print axioms discardWith_total
#print axioms DISCARD_total
end M6.Source.ActualCommandMacros

