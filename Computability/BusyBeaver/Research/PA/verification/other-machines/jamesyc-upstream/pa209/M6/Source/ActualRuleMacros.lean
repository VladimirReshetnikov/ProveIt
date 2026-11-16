module
public import M6.Source.ActualHeadSelectors
@[expose] public section
namespace M6.Source.ActualCommandMacros
open Cantor Enumeration
open AXCode (wim wal)

def genTail (i : Nat) : List Command :=
  ((PUSH ++ J i) ++ [.shift]) ++ ([.ax i 0 0] ++ List.replicate 10 .shift)

/-- Generalization suffix never tests the incoming proved top against zero. -/
theorem genTail_total (i x w : Nat) :
    commandsEval (genTail i) ⟨x,w,0,0⟩ = some ⟨wal i x,w,0,0⟩ := by
  unfold genTail
  refine append_total (m := ⟨0,w,i,x⟩) ?_ (AX_shift10 i 0 0 0 w i x)
  refine append_total (append_total (PUSH_total x w 0 0) (J_total i (pair x w))) ?_
  simp [commandsEval,commandEval,decode_pair]

def mpTail (b : Nat) : List Command :=
  ([.shift,.shift,.mp b] ++ ([.ax b 0 0] ++ List.replicate 10 .shift)) ++ [.shift]

theorem mpPrefix (a b w : Nat) :
    commandsEval [.shift,.shift,.mp b] ⟨0,pair a (pair (wim a b) w),0,0⟩ =
      if a=1 then none else some ⟨b,pair 0 w,b,0⟩ := by
  by_cases ha : a=1 <;> simp [commandsEval,commandEval,decode_pair,ha]

/-- Modus ponens may halt early on antecedent one, otherwise returns its
consequent even when that consequent itself is one. -/
theorem mpTail_result (a b w : Nat) :
    commandsEval (mpTail b) ⟨0,pair a (pair (wim a b) w),0,0⟩ =
      if a=1 then none else some ⟨b,w,0,0⟩ := by
  by_cases ha : a=1
  · rw [mpTail,commandsEval_append,commandsEval_append,mpPrefix,ite_eq_left ha]
    simp only [ha,ite_true,Option.bind_none]
  · rw [ite_eq_right ha]
    unfold mpTail
    refine append_total (m := ⟨wal b 0,pair 0 w,0,b⟩) ?_ ?_
    · refine append_total (m := ⟨b,pair 0 w,b,0⟩) ?_ (AX_shift10 b 0 0 b (pair 0 w) b 0)
      simpa only [ite_eq_right ha] using mpPrefix a b w
    · simp [commandsEval,commandEval,decode_pair]
#print axioms genTail_total
#print axioms mpTail_result
end M6.Source.ActualCommandMacros

