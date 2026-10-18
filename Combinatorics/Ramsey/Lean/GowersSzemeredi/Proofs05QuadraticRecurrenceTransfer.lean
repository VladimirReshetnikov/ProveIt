import GowersSzemeredi.Proofs05QuadraticRecurrenceBudget
import GowersSzemeredi.Proofs05ModularApproximation

/-! Assemble a quadratic recurrence from a low Fourier frequency, a rational
approximation, and the normalized Weyl inequality. The existence of those
analytic inputs is not assumed silently and remains a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadratic_recurrence_of_weyl_witness {N R q : Nat} [NeZero N]
    (a r : ZMod N) (b : Int) (hR : 2 ≤ R) (hq : 0 < q) (hr : r ≠ 0)
    (hrsize : (centeredAbs r : Real) ≤ 4 * (R : Real) ^ 2)
    (happrox : |(-(a * r).valMinAbs : Real) / N - (b : Real) / q| ≤
      ((q : Real) * quadraticRecurrenceSample R)⁻¹)
    (hweyl : 1 / (64 * (R : Real) ^ 2) ≤
      2 ^ (25 : Nat) * quadraticRecurrenceRoot R *
        ((q : Real)⁻¹ + 2 / quadraticRecurrenceSample R) *
          (1 + Real.log (quadraticRecurrenceSample R))) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ 2 ^ 256 * R ^ 16 ∧
      (centeredAbs (((p : ZMod N) ^ 2) * a) : Real) < (N : Real) / R := by
  have hRr : (2 : Real) ≤ R := by exact_mod_cast hR
  have hqr : (0 : Real) < q := by exact_mod_cast hq
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hT : 0 < quadraticRecurrenceSample R := by unfold quadraticRecurrenceSample; positivity
  have hs : 0 < centeredAbs r := Int.natAbs_pos.mpr (mt (ZMod.valMinAbs_eq_zero r).mp hr)
  -- the witness `p = |r| q` satisfies `p < T / R² ≤ T / R ≤ T`, `T` the sample length
  have hpb : ((centeredAbs r * q : Nat) : Real) < quadraticRecurrenceSample R / (R : Real) ^ 2 := by
    simpa only [Nat.cast_mul] using quadraticRecurrence_witness_budget hRr hrsize hqr.le
      (quadraticRecurrence_denominator_bound hRr hqr hweyl)
  have hpR : ((centeredAbs r * q : Nat) : Real) < quadraticRecurrenceSample R / R :=
    hpb.trans_le (div_le_div_of_nonneg_left hT.le (by positivity)
      (by linarith [mul_le_mul_of_nonneg_left hRr (by positivity : (0 : Real) ≤ R)]))
  refine ⟨centeredAbs r * q, Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩
  · have hc : ((centeredAbs r * q : Nat) : Real) ≤ ((2 ^ 256 * R ^ 16 : Nat) : Real) := by
      rw [quadraticRecurrenceSample_natCast]
      exact (hpR.trans_le (div_le_self hT.le (by linarith))).le
    exact_mod_cast hc
  · have hcenter :=
      modular_monomial_of_rational_approximation (k := 2) a r b (by omega) hq hT happrox
    simp only [Nat.reduceSub, pow_one] at hcenter
    calc _ ≤ (N : Real) / quadraticRecurrenceSample R * (centeredAbs r * q : Nat) := hcenter
      _ < (N : Real) / quadraticRecurrenceSample R * (quadraticRecurrenceSample R / R) :=
        mul_lt_mul_of_pos_left hpR (by positivity)
      _ = (N : Real) / R := by field_simp

end LeanProofs.GowersSzemeredi
