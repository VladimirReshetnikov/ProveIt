import GowersSzemeredi.Proofs05PolynomialPartition
import GowersSzemeredi.Proofs05RecurrenceFourierScale

/-! Excluding recurrence at radius `N/R` produces a small nonzero Fourier
frequency with a Weyl sum of size at least `t/(8R)`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem polynomial_recurrence_fourier_witness {N R k t : Nat} [NeZero N]
    (a : ZMod N) (hR : 2 ≤ R) (ht : 2 ≤ t) (htN : t ≤ N) (hNR : 4 * R ≤ N)
    (hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (N : Real) / R ≤ (centeredAbs (((p : ZMod N) ^ k) * a) : Real)) :
    ∃ r : ZMod N, r ≠ 0 ∧ (centeredAbs r : Real) ≤ 4 * (R : Real) ^ 2 ∧
      (t : Real) / (8 * R) ≤ ‖weylSum (-(a * r).valMinAbs / (N : Real)) k t‖ := by
  obtain ⟨M, hM, hMeven, hMN, hMlo, hMhi⟩ := recurrence_fourier_interval_scale hR hNR
  obtain ⟨r, hr, hrsize, hrnorm⟩ := polynomial_missing_interval_witness_at_scale
    (k := k) a (M : Real) ht htN hM hMeven hMN le_rfl
    (fun p hp hpt => hMhi.trans_le (hno p hp hpt))
  refine ⟨r, hr, hrsize.trans ?_, ?_⟩
  · exact recurrence_fourier_frequency_bound (by omega) hM hMlo
  · exact (recurrence_fourier_norm_lower (NeZero.pos N) (by omega) hMlo).trans hrnorm

end LeanProofs.GowersSzemeredi
