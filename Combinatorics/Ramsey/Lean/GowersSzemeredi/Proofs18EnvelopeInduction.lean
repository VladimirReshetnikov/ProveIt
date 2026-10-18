import GowersSzemeredi.Proofs18UniformCovers
import GowersSzemeredi.Proofs16AbstractFamily

/-! Shared setup for the discrepancy and polynomial envelope inductions.

`classCovers_of_profiles` is in `Proofs18EnvelopeInductionSide`, outside the
final route. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Propagate any envelope predicate from degree three along its budget recurrence. -/
theorem envelope_induction {P : Nat → Nat → Prop} {budget : Nat → Nat}
    {step : Nat → Nat → Nat}
    (hstep : ∀ k, 2 ≤ k → ∀ μ, P (k + 1) μ → P (k + 2) (step k μ))
    (hbase : P 3 (budget 1))
    (hrec : ∀ k, 1 ≤ k → budget (k + 1) = step (k + 1) (budget k)) :
    ∀ k, 1 ≤ k → P (k + 2) (budget k) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact hbase
  | succ k hk ih =>
    rw [hrec k hk]
    exact hstep (k + 1) (by omega) (budget k) ih

end LeanProofs.GowersSzemeredi
