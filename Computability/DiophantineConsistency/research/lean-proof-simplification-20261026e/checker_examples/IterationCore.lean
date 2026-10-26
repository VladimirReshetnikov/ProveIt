/-!
Proof-only adapters for the existing Nat.rec definitions.
No executable scanner, wire representation, or supplied PR program is changed.
This module intentionally uses only Lean's implicit Init import.

Status: authored candidate; not compiler-checked at file creation.
-/
namespace CheckerRefactor

universe u v

/-- Iteration preserves an already stationary state. -/
theorem rec_fixed {α : Sort u} (step : α → α) (n : Nat) (x : α)
    (hx : step x = x) : n.rec x (fun _ acc => step acc) = x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (n.rec x (fun _ acc => step acc)) = x
    rw [ih, hx]

/-- Move the first transition out of a tail-recursive iteration. -/
theorem rec_succ_right {α : Sort u} (step : α → α) (n : Nat) (x : α) :
    (n + 1).rec x (fun _ acc => step acc) =
      n.rec (step x) (fun _ acc => step acc) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step ((n + 1).rec x (fun _ acc => step acc)) =
      step (n.rec (step x) (fun _ acc => step acc))
    exact congrArg step ih

/-- Encoding commutes with iteration when it commutes with one transition.
This is the Nat.rec-shaped version of Function.Semiconj.iterate_right. -/
theorem rec_fusion {α : Sort u} {β : Sort v}
    (step : α → α) (codedStep : β → β) (encode : α → β)
    (commutes : ∀ x, codedStep (encode x) = encode (step x))
    (n : Nat) (x : α) :
    n.rec (encode x) (fun _ acc => codedStep acc) =
      encode (n.rec x (fun _ acc => step acc)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change codedStep (n.rec (encode x) (fun _ acc => codedStep acc)) =
      encode (step (n.rec x (fun _ acc => step acc)))
    rw [ih, commutes]

/-- One invariant lemma also covers scan_sound-style safety arguments. -/
theorem rec_preserves {α : Sort u} (step : α → α) (P : α → Prop)
    (stable : ∀ x, P x → P (step x)) (n : Nat) (x : α) (hx : P x) :
    P (n.rec x (fun _ acc => step acc)) := by
  induction n with
  | zero => exact hx
  | succ n ih => exact stable _ ih

#print axioms rec_fixed
#print axioms rec_succ_right
#print axioms rec_fusion
#print axioms rec_preserves

end CheckerRefactor
