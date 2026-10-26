import Init

namespace DiophantineConsistency.ProofSimplification

/-- A reusable alternative when the new proof should avoid function extensionality. -/
theorem rec_congr {α : Sort u} (a b : α) (f g : Nat → α → α)
    (hab : a = b) (hfg : ∀ i x, f i x = g i x) (n : Nat) :
    Nat.rec (motive := fun _ => α) a f n =
      Nat.rec (motive := fun _ => α) b g n := by
  induction n with
  | zero => exact hab
  | succ n ih => exact (congrArg (f n) ih).trans (hfg n _)

#print axioms rec_congr

end DiophantineConsistency.ProofSimplification
