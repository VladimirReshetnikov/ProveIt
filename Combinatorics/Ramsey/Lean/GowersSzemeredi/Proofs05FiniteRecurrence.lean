import GowersSzemeredi.Proofs05FiniteWeylNormalization
import GowersSzemeredi.Proofs05FiniteRecurrenceTransfer
import GowersSzemeredi.Proofs05FiniteRecurrenceBudget
import GowersSzemeredi.Proofs05RecurrenceFourierWitness

/-! Assemble polynomial recurrence from a single explicit finite Weyl
budget. Choosing and comparing degree-dependent numerical scales remains
separate from the analytic and modular argument. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem polynomial_recurrence_of_finite_weyl_budget {N R k t m : Nat} [NeZero N]
    (a : ZMod N) (hk : 2 ≤ k) (hR : 2 ≤ R) (hkt : k ≤ t) (hm : 1 ≤ m)
    (hRt : 4 * R ≤ t) (htN : t ≤ N)
    (hbudget : 16 * (8 * (R : Real)) ^ weylDifferencingPower k * (R : Real) ^ 3 *
      (weylRaisedCoefficientAt k m *
        (t : Real) ^ ((((k - 1 : Nat) : Real) ^ 2) / m) * (1 + Real.log t)) ≤ t) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ t ∧
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) < (N : Real) / R := by
  classical
  have ht : 2 ≤ t := by omega
  have ht0 : (0 : Real) < t := by exact_mod_cast (show 0 < t by omega)
  have hR0 : (0 : Real) < R := by exact_mod_cast (show 0 < R by omega)
  by_contra hfail
  have hno : ∀ p : Nat, 1 ≤ p → p ≤ t →
      (N : Real) / R ≤ (centeredAbs (((p : ZMod N) ^ k) * a) : Real) := by
    intro p hp hpt
    by_contra h
    exact hfail ⟨p, hp, hpt, lt_of_not_ge h⟩
  obtain ⟨r, hr, hrsize, hrnorm⟩ := polynomial_recurrence_fourier_witness a hR ht htN
    (hRt.trans htN) hno
  let alpha : Real := -(a * r).valMinAbs / (N : Real)
  obtain ⟨b, q, hq, hqt, hbq, happrox⟩ := lemma_5_4_holds alpha (t ^ (k - 1))
    (one_le_pow₀ (by omega))
  have happrox' : |alpha - (b : Real) / q| ≤ ((q : Real) * (t : Real) ^ (k - 1))⁻¹ := by
    simpa only [Nat.cast_pow] using happrox
  let W := weylDifferencingPower k
  let A := (8 * (R : Real)) ^ W
  let D := weylRaisedCoefficientAt k m *
    (t : Real) ^ ((((k - 1 : Nat) : Real) ^ 2) / m) * (1 + Real.log t)
  have hlower : 1 / A ≤ ‖weylSum alpha k t‖ ^ W / (t : Real) ^ W := by
    have hsq := pow_le_pow_left₀ (show (0 : Real) ≤ (t : Real) / (8 * R) by positivity) hrnorm W
    calc
      _ = ((t : Real) / (8 * R)) ^ W / (t : Real) ^ W := by
        dsimp [A]
        rw [div_pow]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hsq (by positivity)
  have hupper := weyl_normalized_finite hk ht hkt hm (by omega) hqt b alpha hbq happrox'
  have hweyl : 1 / A ≤ D * ((q : Real)⁻¹ + 2 / t) := by
    calc
      _ ≤ _ := hlower.trans hupper
      _ = _ := by dsimp [D]; ring
  have hD : 0 ≤ D := by
    have ht1 : (1 : Real) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
    have hlog : 0 ≤ 1 + Real.log (t : Real) := by linarith [Real.log_nonneg ht1]
    dsimp [D, weylRaisedCoefficientAt]
    positivity
  have hsmall := finite_recurrence_frequency_budget (R := (R : Real))
    (by exact_mod_cast (show 1 ≤ R by omega)) ht0 (show 0 < A by dsimp [A]; positivity)
    hD (show (0 : Real) < q by exact_mod_cast (show 0 < q by omega)) hrsize hweyl hbudget
  exact hfail (polynomial_recurrence_of_dirichlet_witness a r b hk (by omega) (by omega)
    (by omega) hr happrox' hsmall)

end LeanProofs.GowersSzemeredi
