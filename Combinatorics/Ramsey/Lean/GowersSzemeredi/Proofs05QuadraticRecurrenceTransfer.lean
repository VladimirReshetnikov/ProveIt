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
  have hR0 : (0 : Real) < R := by linarith
  have hqr : (0 : Real) < q := by exact_mod_cast hq
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hT : 0 < quadraticRecurrenceSample R := by
    unfold quadraticRecurrenceSample
    positivity
  have hs : 0 < centeredAbs r := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hv : r.valMinAbs = 0 := Int.natAbs_eq_zero.mp hz
    exact hr ((ZMod.valMinAbs_eq_zero r).mp hv)
  let p := centeredAbs r * q
  have hp : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr (by dsimp [p]; positivity)
  have hqb := quadraticRecurrence_denominator_bound hRr hqr hweyl
  have hpb : (p : Real) < quadraticRecurrenceSample R / (R : Real) ^ 2 := by
    simpa only [p, Nat.cast_mul] using
      quadraticRecurrence_witness_budget hRr hrsize hqr.le hqb
  have hRone : (1 : Real) ≤ (R : Real) ^ 2 := one_le_pow₀ (by linarith)
  have hpT : (p : Real) < quadraticRecurrenceSample R :=
    hpb.trans_le ((div_le_iff₀ (by positivity)).mpr
      (by nlinarith [mul_le_mul_of_nonneg_left hRone hT.le]))
  have hpNat : p ≤ 2 ^ 256 * R ^ 16 := by
    have hc : (p : Real) ≤ ((2 ^ 256 * R ^ 16 : Nat) : Real) := by
      rw [quadraticRecurrenceSample_natCast]
      exact hpT.le
    exact_mod_cast hc
  have hcenter : (centeredAbs (((p : ZMod N) ^ 2) * a) : Real) ≤
      ((N : Real) / quadraticRecurrenceSample R) * (p : Real) := by
    simpa only [Nat.reduceSub, pow_one] using
      modular_monomial_of_rational_approximation (k := 2) a r b (by omega) hq hT happrox
  refine ⟨p, hp, hpNat, hcenter.trans_lt ?_⟩
  have hpR : (p : Real) < quadraticRecurrenceSample R / R := by
    apply hpb.trans_le
    apply div_le_div_of_nonneg_left hT.le hR0
    nlinarith
  calc
    _ < ((N : Real) / quadraticRecurrenceSample R) * (quadraticRecurrenceSample R / R) :=
      mul_lt_mul_of_pos_left hpR (by positivity)
    _ = (N : Real) / R := by field_simp

end LeanProofs.GowersSzemeredi
