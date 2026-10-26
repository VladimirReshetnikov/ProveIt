import Mathlib.Logic.Function.Iterate

/-!
Preferred production version: one bridge to the existing mathlib iteration
API, rather than a second iteration library. The executable Nat.rec terms
remain untouched. Exact pinned-mathlib elaboration remains to be checked.
-/
namespace CheckerRefactor.MathlibAdapter

universe u v

/-- Nat.rec is left-oriented; Nat.iterate is right-oriented. -/
theorem rec_eq_iterate {α : Type u} (step : α → α) (n : Nat) (x : α) :
    n.rec x (fun _ acc => step acc) = step^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (n.rec x (fun _ acc => step acc)) = step^[n + 1] x
    rw [Function.iterate_succ_apply', ih]

theorem rec_fixed {α : Type u} (step : α → α) (n : Nat) (x : α)
    (hx : step x = x) : n.rec x (fun _ acc => step acc) = x := by
  rw [rec_eq_iterate]
  exact Function.iterate_fixed hx n

theorem rec_succ_right {α : Type u} (step : α → α) (n : Nat) (x : α) :
    (n + 1).rec x (fun _ acc => step acc) =
      n.rec (step x) (fun _ acc => step acc) := by
  rw [rec_eq_iterate, rec_eq_iterate]
  rfl

theorem rec_fusion {α : Type u} {β : Type v}
    (step : α → α) (codedStep : β → β) (encode : α → β)
    (commutes : ∀ x, codedStep (encode x) = encode (step x))
    (n : Nat) (x : α) :
    n.rec (encode x) (fun _ acc => codedStep acc) =
      encode (n.rec x (fun _ acc => step acc)) := by
  rw [rec_eq_iterate, rec_eq_iterate]
  have h : Function.Semiconj encode step codedStep := fun a => (commutes a).symm
  exact (h.iterate_right n x).symm

end CheckerRefactor.MathlibAdapter
