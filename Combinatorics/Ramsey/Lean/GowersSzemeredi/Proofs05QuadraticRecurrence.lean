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
  classical
  let t := 2 ^ 256 * R ^ 16
  have htlarge : 4 * R ≤ t := quadraticRecurrenceSample_nat_large hR
  have ht : 2 ≤ t := by omega
  have htR : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hRr : (0 : Real) < R := by exact_mod_cast (show 0 < R by omega)
  have htcast : (t : Real) = quadraticRecurrenceSample R := quadraticRecurrenceSample_natCast R
  by_contra hfail
  have hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (N : Real) / R ≤ (centeredAbs (((p : ZMod N) ^ 2) * a) : Real) := by
    intro p hp hpt
    by_contra h
    exact hfail ⟨p, hp, hpt, lt_of_not_ge h⟩
  obtain ⟨r, hr, hrsize, hrnorm⟩ := polynomial_recurrence_fourier_witness a hR ht hN
    (htlarge.trans hN) hno
  let alpha : Real := -(a * r).valMinAbs / (N : Real)
  obtain ⟨b, q, hq, hqt, hbq, happrox⟩ := lemma_5_4_holds alpha t (by omega)
  have hlower : 1 / (64 * (R : Real) ^ 2) ≤ ‖weylSum alpha 2 t‖ ^ 2 / (t : Real) ^ 2 := by
    have hsq := pow_le_pow_left₀ (show (0 : Real) ≤ (t : Real) / (8 * R) by positivity) hrnorm 2
    calc
      _ = ((t : Real) / (8 * R)) ^ 2 / (t : Real) ^ 2 := by field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_right hsq (by positivity)
  have hupper := quadratic_weyl_normalized ht (by omega) hqt b alpha hbq happrox
  have hweyl := hlower.trans hupper
  rw [htcast, quadraticRecurrenceSample_sqrt] at hweyl
  have happrox' : |(-(a * r).valMinAbs : Real) / N - (b : Real) / q| ≤
      ((q : Real) * quadraticRecurrenceSample R)⁻¹ := by
    simpa only [alpha, htcast] using happrox
  exact hfail (quadratic_recurrence_of_weyl_witness a r b hR (by omega) hr hrsize happrox' hweyl)

end LeanProofs.GowersSzemeredi
