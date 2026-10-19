import GowersSzemeredi.Proofs05QuadraticWeyl
import GowersSzemeredi.Proofs05RecurrenceFourierWitness
import GowersSzemeredi.Proofs05QuadraticRecurrenceTransfer

/-! A finite quadratic recurrence with an explicit polynomial dependence on
the reciprocal radius. This assembles the Fourier, Dirichlet, Weyl, and
modular approximation arguments without an asymptotic size hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadratic_recurrence {N R : Nat} [NeZero N] (a : ZMod N)
    (hR : 2 ≤ R) (hN : 2 ^ 256 * R ^ 16 ≤ N) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ 2 ^ 256 * R ^ 16 ∧
      (centeredAbs (((p : ZMod N) ^ 2) * a) : Real) < (N : Real) / R := by
  let t := 2 ^ 256 * R ^ 16
  have htlarge : 4 * R ≤ t := quadraticRecurrenceSample_nat_large hR
  have ht : 2 ≤ t := by omega
  have htcast : (t : Real) = quadraticRecurrenceSample R := quadraticRecurrenceSample_natCast R
  by_contra! hfail
  obtain ⟨r, hr, hrsize, hrnorm⟩ := polynomial_recurrence_fourier_witness a hR ht hN
    (htlarge.trans hN) hfail
  let alpha : Real := -(a * r).valMinAbs / (N : Real)
  obtain ⟨b, q, hq, hqt, hbq, happrox⟩ := lemma_5_4_holds alpha t (by omega)
  have hlower : 1 / (64 * (R : Real) ^ 2) ≤ ‖weylSum alpha 2 t‖ ^ 2 / (t : Real) ^ 2 :=
    calc _ = ((t : Real) / (8 * R)) ^ 2 / (t : Real) ^ 2 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hrnorm 2)
        (by positivity)
  have hweyl := hlower.trans (quadratic_weyl_normalized ht (by omega) hqt b alpha hbq happrox)
  rw [htcast, quadraticRecurrenceSample_sqrt] at hweyl
  obtain ⟨p, hp, hpt, hlt⟩ := quadratic_recurrence_of_weyl_witness a r b hR (by omega) hr hrsize
    (by simpa only [alpha, htcast] using happrox) hweyl
  exact absurd hlt (not_lt.mpr (hfail p hp hpt))

end LeanProofs.GowersSzemeredi
