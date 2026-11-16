module
public import M6.Source.CommandStore
@[expose] public section

/-! Operational contracts of the exact arithmetic compiler macros, including
saved top1 and the Cantor zero alias. Literal source transfer is separate. -/
namespace M6.Source.ActualCommandMacros
open Cantor Enumeration ActualAXCode
open AXCode (wim wal wn wex wa)

def D : List Command := [.ax 0 0 0]
def H : List Command := D ++ List.replicate 11 .shift
def PUSH : List Command := D ++ List.replicate 9 .shift ++ [.mp 0]
def DISCARD : List Command := [.mp 1,.ax 1 0 0] ++ List.replicate 10 .shift ++ [.mp 0]
def J (u : Nat) : List Command := if u = 0 then [] else [.mp u]

theorem ax_step (c x y : Nat) (s : CommandStore) :
    commandEval (.ax c x y) s = some ⟨gate (s.d+x) (s.h+y) c,
      (pa135Heads (s.d+x) (s.h+y) c s.d s.h ++ [s.t]).foldr pair s.w,0,0⟩ := by rfl

@[simp] theorem wim_ne_one (a b : Nat) : wim a b ≠ 1 := by
  simp only [AXCode.wim,implication]; omega

@[simp] theorem wim_sum_ne_one (a b c d : Nat) : wim a b + wim c d ≠ 1 := by
  simp only [AXCode.wim,implication]; omega

@[simp] theorem wal_add_ne_one (a b t : Nat) : wal a b + t ≠ 1 := by
  simp only [AXCode.wal,universal]; omega

@[simp] theorem add_wal_ne_one (a b t : Nat) : t + wal a b ≠ 1 := by
  simp only [AXCode.wal,universal]; omega

@[simp] theorem wim_ne_wal (a b c d : Nat) : wim a b ≠ wal c d := by
  simp only [AXCode.wim,AXCode.wal,implication,universal]; omega

@[simp] theorem gate_ne_one (a b c : Nat) : gate a b c ≠ 1 := by
  unfold gate
  split
  · omega
  · simp [bundle,wn]

@[simp] theorem wim_one_ne_zero (a : Nat) : wim a 1 ≠ 0 := by
  have h := M6.Source.Enumeration.pair_bounds a 1
  simp only [AXCode.wim,implication]; omega

@[simp] theorem wim_wal_zero_ne_zero (a b : Nat) : wim (wal a b) 0 ≠ 0 := by
  have hw : 2 ≤ wal a b := by simp only [AXCode.wal,universal]; omega
  have hp := M6.Source.Enumeration.pair_bounds (wal a b) 0
  simp only [AXCode.wim,implication]; omega

/-- H pops one encoded stack entry and preserves the old top, even top=1. -/
theorem H_total (t x w d h : Nat) :
    commandsEval H ⟨t,pair x w,d,h⟩ = some ⟨t,w,0,x⟩ := by
  simp only [H,D,List.replicate_succ,List.replicate_zero,
    commandsEval,ax_step,Option.bind_some,pa135Heads,List.cons_append,List.nil_append,List.foldr_cons,List.foldr_nil]
  simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]

/-- PUSH saves an arbitrary incoming top and resets both working caches. -/
theorem PUSH_total (t w d h : Nat) :
    commandsEval PUSH ⟨t,w,d,h⟩ = some ⟨0,pair t w,0,0⟩ := by
  simp only [PUSH,D,List.replicate_succ,List.replicate_zero,
    List.cons_append,List.nil_append,commandsEval,ax_step,Option.bind_some,pa135Heads,
    List.cons_append,List.nil_append,List.foldr_cons,List.foldr_nil]
  simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]

/-- Symbolic ten-shift frame discharge; avoids normalizing closed axiom codes. -/
theorem AX_shift10 (c x y t w d h : Nat) :
    commandsEval ([.ax c x y] ++ List.replicate 10 .shift) ⟨t,w,d,h⟩ = some ⟨wal d h,w,0,t⟩ := by
  simp only [List.replicate_succ,List.replicate_zero,
    List.cons_append,List.nil_append,commandsEval,ax_step,Option.bind_some,pa135Heads,
    List.foldr_cons,List.foldr_nil]
  simp [commandEval,decode_pair,rho1,rho2,rho3,rho4,rho5,rho6,rho7,rho8,AXCode.rho1,AXCode.rho2,AXCode.rho4,AXCode.rho6,AXCode.rho8,wex,wn]

theorem J_total (u w : Nat) : commandsEval (J u) ⟨0,w,0,0⟩ = some ⟨0,w,u,0⟩ := by
  by_cases hu : u = 0
  · simp [J,hu,commandsEval]
  · have hp := M6.Source.Enumeration.pair_bounds 0 u
    have he : wim 0 u ≠ 0 := by simp only [AXCode.wim,implication]; omega
    simp [J,hu,commandsEval,commandEval,he]

#print axioms AX_shift10
#print axioms H_total
#print axioms PUSH_total
#print axioms J_total
end M6.Source.ActualCommandMacros

