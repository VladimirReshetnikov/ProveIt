import DiophantineConsistency.SplitCertificate59
import SourceGuardRecovery
import Mathlib.Tactic.LinearCombination

namespace FreshSimplifications

/-- A concrete theorem for the literal current source rows. Only register 24
needs a positivity hypothesis; naturalness supplies the remaining signs. -/
theorem source_port_guard (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hL : 0 < x 24)
    (hs : ∀ k, DiophantineConsistency.SplitCertificate59.sourceRows ports
      (fun i => (x i : ℤ)) k = 0) :
    0 < x 0 ∧ 0 < ports 0 ∧ 8 ≤ x 16 := by
  have h0 := hs 0
  have h1 := hs 1
  change (x 24 : ℤ) + ((-2) * ports 0) * x 0 +
    (-(ports 0 ^ 2)) * ((x 0 : ℤ) ^ 2) = 0 at h0
  change (-1 : ℤ) + (-1) * x 24 + x 16 + (-ports 0) * x 0 +
    (-ports 0) * ((x 0 : ℤ) * x 24) = 0 at h1
  have hLrow : (x 24 : ℤ) = (1 + (x 0 : ℤ) * ports 0)^2 - 1 := by
    linear_combination h0
  have hNrow : (x 16 : ℤ) = (1 + (x 0 : ℤ) * ports 0) * (1 + x 24) := by
    linear_combination h1
  have hp := port_pos_of_scale_rows (Nat.cast_nonneg (x 0))
    (by exact_mod_cast hL) (Nat.cast_nonneg (x 16)) hLrow hNrow
  have h8 := eight_le_scale_of_rows (Nat.cast_nonneg (x 0))
    (by exact_mod_cast hL) (Nat.cast_nonneg (x 16)) hLrow hNrow
  exact ⟨by exact_mod_cast hp.1, hp.2.1, by exact_mod_cast h8⟩

/-- The bootstrap bound no longer needs an independent positive-port guard. -/
theorem source_Y_ge_two_no_beta (ports : Fin 4 → ℤ) (x : Fin 31 → ℕ)
    (hL : 0 < x 24) (hw : 0 < x 9)
    (hs : ∀ k, DiophantineConsistency.SplitCertificate59.sourceRows ports
      (fun i => (x i : ℤ)) k = 0) : 2 ≤ x 16 * x 9 := by
  have h8 := (source_port_guard ports x hL hs).2.2
  nlinarith

#print axioms source_port_guard
#print axioms source_Y_ge_two_no_beta
end FreshSimplifications
