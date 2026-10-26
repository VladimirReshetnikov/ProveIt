import Init

/-! Recursor-level scanner lemmas. They do not change any scanner definition. -/

namespace DiophantineConsistency.ProofSimplification

theorem rec_fixed {α : Sort u} (step : α → α) (a : α) (h : step a = a)
    (fuel : Nat) : fuel.rec a (fun _ acc => step acc) = a := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step (fuel.rec a (fun _ acc => step acc)) = a
    rw [ih, h]

theorem rec_succ_left {α : Sort u} (step : α → α) (a : α) (fuel : Nat) :
    Nat.rec (motive := fun _ => α) a (fun _ acc => step acc) (fuel + 1) =
      Nat.rec (motive := fun _ => α) (step a) (fun _ acc => step acc) fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    change step ((fuel + 1).rec a (fun _ acc => step acc)) =
      step (fuel.rec (step a) (fun _ acc => step acc))
    rw [ih]

theorem rec_invariant {α : Sort u} (step : α → α) (P : α → Prop)
    (hstep : ∀ a, P a → P (step a)) (a : α) (ha : P a) (fuel : Nat) :
    P (fuel.rec a (fun _ acc => step acc)) := by
  induction fuel with
  | zero => exact ha
  | succ fuel ih => exact hstep _ ih

#print axioms rec_fixed
#print axioms rec_succ_left
#print axioms rec_invariant

end DiophantineConsistency.ProofSimplification
