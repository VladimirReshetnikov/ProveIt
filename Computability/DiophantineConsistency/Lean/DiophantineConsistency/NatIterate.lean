import Init

/-! Recursor facts for numeric scanners, without changing their executable definitions. -/
namespace DiophantineConsistency.NatIterate

theorem rec_fixed {α : Sort u} (step : α → α) (a : α) (h : step a = a)
    (fuel : Nat) : fuel.rec a (fun _ acc => step acc) = a := by
  induction fuel with
  | zero => rfl
  | succ _ ih => exact (congrArg step ih).trans h

theorem rec_succ {α : Sort u} (step : α → α) (a : α) (fuel : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ acc => step acc) (fuel + 1) =
      Nat.rec (motive := fun _ => α) (step a) (fun _ acc => step acc) fuel := by
  induction fuel with
  | zero => rfl
  | succ _ ih => exact congrArg step ih

end DiophantineConsistency.NatIterate
