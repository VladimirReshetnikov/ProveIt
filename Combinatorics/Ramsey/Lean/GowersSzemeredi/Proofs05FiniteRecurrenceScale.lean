import GowersSzemeredi.Proofs05FiniteRecurrence
import GowersSzemeredi.Proofs05FiniteWeylRootBudget

/-! An explicit finite sample for recurrence in every degree. Its dependence
on the reciprocal radius is polynomial, before any comparison with the
paper's localization constants. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def finiteRecurrenceDivisor (k : Nat) : Nat := (k - 1) ^ 2 + 1

def finiteWeylCoefficient (k m : Nat) : Nat :=
  2 ^ (weylDifferencingPower k + 2 * k + 12) * Nat.factorial k *
    m ^ ((k - 1) * 2 ^ m) * (k + 1)

def finiteRecurrenceBase (k R : Nat) : Nat :=
  let m := finiteRecurrenceDivisor k
  16 * 8 ^ weylDifferencingPower k * finiteWeylCoefficient k m * (2 * m + 1) *
    R ^ (weylDifferencingPower k + 3)

def finiteRecurrenceSample (k R : Nat) : Nat :=
  finiteRecurrenceBase k R ^ (2 * finiteRecurrenceDivisor k)

theorem finiteWeylCoefficient_cast (k m : Nat) :
    (finiteWeylCoefficient k m : Real) = weylRaisedCoefficientAt k m := by
  simp only [finiteWeylCoefficient, weylRaisedCoefficientAt, Nat.cast_mul,
    Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]

theorem finiteWeylCoefficient_ge_degree {k m : Nat} (hm : 1 ≤ m) :
    k + 1 ≤ finiteWeylCoefficient k m := by
  have hp : 1 ≤ 2 ^ (weylDifferencingPower k + 2 * k + 12) * Nat.factorial k *
      m ^ ((k - 1) * 2 ^ m) := by
    apply Nat.one_le_iff_ne_zero.mpr
    have hfac := Nat.factorial_pos k
    positivity
  simpa only [one_mul, finiteWeylCoefficient] using (Nat.mul_le_mul_right (k + 1) hp)

theorem finiteRecurrenceBase_large {k R : Nat} (hR : 1 ≤ R) :
    k + 1 ≤ finiteRecurrenceBase k R ∧ 4 * R ≤ finiteRecurrenceBase k R := by
  let m := finiteRecurrenceDivisor k
  have hm : 1 ≤ m := by dsimp [m, finiteRecurrenceDivisor]; omega
  have hC := finiteWeylCoefficient_ge_degree (k := k) hm
  have hC1 : 1 ≤ finiteWeylCoefficient k m := by omega
  have hpow : R ≤ R ^ (weylDifferencingPower k + 3) := by
    simpa only [pow_one] using Nat.pow_le_pow_right hR (by omega : 1 ≤ weylDifferencingPower k + 3)
  have h8 : 1 ≤ 8 ^ weylDifferencingPower k := one_le_pow₀ (by omega)
  have hlow : 16 * finiteWeylCoefficient k m * R ≤ finiteRecurrenceBase k R := by
    change _ ≤ 16 * 8 ^ weylDifferencingPower k * finiteWeylCoefficient k m *
      (2 * m + 1) * R ^ (weylDifferencingPower k + 3)
    calc
      _ = 16 * 1 * finiteWeylCoefficient k m * 1 * R := by ring
      _ ≤ _ := by gcongr; omega
  constructor
  · nlinarith [Nat.mul_le_mul hC hR]
  · nlinarith [Nat.mul_le_mul_right R hC1]

theorem finiteRecurrenceSample_large {k R : Nat} (hR : 1 ≤ R) :
    k + 1 ≤ finiteRecurrenceSample k R ∧ 4 * R ≤ finiteRecurrenceSample k R := by
  have hb := finiteRecurrenceBase_large (k := k) hR
  have hbase : 1 ≤ finiteRecurrenceBase k R := by omega
  have he : 1 ≤ 2 * finiteRecurrenceDivisor k := by dsimp [finiteRecurrenceDivisor]; omega
  have hpow : finiteRecurrenceBase k R ≤ finiteRecurrenceSample k R := by
    simpa only [pow_one, finiteRecurrenceSample] using Nat.pow_le_pow_right hbase he
  exact ⟨hb.1.trans hpow, hb.2.trans hpow⟩

theorem finiteRecurrenceSample_weyl_budget {k R : Nat} (hR : 1 ≤ R) :
    let t := finiteRecurrenceSample k R
    let m := finiteRecurrenceDivisor k
    16 * (8 * (R : Real)) ^ weylDifferencingPower k * (R : Real) ^ 3 *
      (weylRaisedCoefficientAt k m *
        (t : Real) ^ ((((k - 1 : Nat) : Real) ^ 2) / m) * (1 + Real.log t)) ≤ t := by
  let m := finiteRecurrenceDivisor k
  have hm : 1 ≤ m := by dsimp [m, finiteRecurrenceDivisor]; omega
  have hm0 : (0 : Real) < m := by exact_mod_cast (show 0 < m by omega)
  have hbase : (1 : Real) ≤ finiteRecurrenceBase k R := by
    exact_mod_cast (show 1 ≤ finiteRecurrenceBase k R by
      have := finiteRecurrenceBase_large (k := k) hR; omega)
  have hC : 0 ≤ weylRaisedCoefficientAt k m := by rw [← finiteWeylCoefficient_cast]; positivity
  have hexp : (((k - 1 : Nat) : Real) ^ 2) / m = 1 - 1 / (m : Real) := by
    have hmcast : (m : Real) = ((k - 1 : Nat) : Real) ^ 2 + 1 := by
      simp only [m, finiteRecurrenceDivisor, Nat.cast_add, Nat.cast_pow, Nat.cast_one]
    apply (div_eq_iff hm0.ne').mpr
    field_simp
    nlinarith only [hmcast]
  have hscale : (16 * (8 * (R : Real)) ^ weylDifferencingPower k * (R : Real) ^ 3) *
      weylRaisedCoefficientAt k m * (2 * (m : Real) + 1) = (finiteRecurrenceBase k R : Real) := by
    rw [← finiteWeylCoefficient_cast]
    simp only [finiteRecurrenceBase, Nat.cast_mul, Nat.cast_pow, Nat.cast_add,
      Nat.cast_ofNat, Nat.cast_one, mul_pow, pow_add]
    dsimp [m]
    ring
  have h := finite_weyl_budget_at_nat_power hbase hm (by positivity) hC hscale.le
  simpa only [finiteRecurrenceSample, Nat.cast_pow, hexp, m] using h

/-- Polynomial dependence on the reciprocal radius in every fixed degree. -/
theorem polynomial_recurrence_finite {N R k : Nat} [NeZero N]
    (a : ZMod N) (hk : 2 ≤ k) (hR : 2 ≤ R) (hN : finiteRecurrenceSample k R ≤ N) :
    ∃ p : Nat, 1 ≤ p ∧ p ≤ finiteRecurrenceSample k R ∧
      (centeredAbs (((p : ZMod N) ^ k) * a) : Real) < (N : Real) / R := by
  have hlarge := finiteRecurrenceSample_large (k := k) (by omega : 1 ≤ R)
  apply polynomial_recurrence_of_finite_weyl_budget a hk hR (by omega)
    (show 1 ≤ finiteRecurrenceDivisor k by dsimp [finiteRecurrenceDivisor]; omega)
    hlarge.2 hN
  exact finiteRecurrenceSample_weyl_budget (by omega)

end LeanProofs.GowersSzemeredi
