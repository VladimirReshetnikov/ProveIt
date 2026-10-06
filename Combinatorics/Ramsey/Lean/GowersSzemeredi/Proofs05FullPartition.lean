import GowersSzemeredi.Proofs05DegreeBudgets
import GowersSzemeredi.Proofs05Lemma9Scale
import GowersSzemeredi.Proofs05PhaseRemoval
import GowersSzemeredi.Proofs05Lemma14
import GowersSzemeredi.Proofs05Corollary58

/-!
# Unconditional polynomial partition theorems

The degree induction uses residue classes of the recurrence step, removes the
top coefficient after affine substitution, and reserves enough diameter for
both summands. The integer budgets justify every rounding and threshold use.
-/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- A coarse length meeting every hypothesis of the polynomial degree step. -/
theorem polynomial_degree_scale_exists {k r v : Nat} (hk : 1 ≤ k)
    (hthreshold : polynomialPartitionThreshold (k + 1) < r)
    (hv : (v : Real) ≤ (r : Real) ^ (polynomialPartitionConstant (k + 1) : Real)⁻¹) :
    ∃ u : Nat, 1 ≤ u ∧ u ^ 4 ≤ r ∧
      ∀ L : Nat, L = u - 1 ∨ L = u →
        polynomialPartitionThreshold k < L ∧
        (v : Real) ≤ (L : Real) ^ (polynomialPartitionConstant k : Real)⁻¹ ∧
        polynomialDegreeStepError r u (k + 1) +
          (L : Real) ^ (-(2 * (polynomialPartitionConstant k : Real)⁻¹)) ≤
          (r : Real) ^ (-(2 * (polynomialPartitionConstant (k + 1) : Real)⁻¹)) := by
  let K := polynomialPartitionConstant k
  let D := polynomialPartitionConstant (k + 1)
  let E := (k + 1) ^ 2 * 2 ^ (2 * (k + 1))
  let x : Real := (r : Real) ^ (D : Real)⁻¹
  have hK : 1 ≤ K := by
    dsimp [K, polynomialPartitionConstant]
    exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hE : 0 < E := by dsimp [E]; positivity
  have hD : D = 2 * E * K := polynomialPartitionConstant_succ k
  obtain ⟨hD8, hgamma⟩ := polynomialPartitionConstant_degree_budgets hk
  have hDpos : 0 < D := by change 8 * K ≤ D at hD8; omega
  have hDreal : (D : Real) ≠ 0 := by exact_mod_cast hDpos.ne'
  have hr0 : (0 : Real) ≤ r := Nat.cast_nonneg _
  have hx0 : 0 ≤ x := Real.rpow_nonneg hr0 _
  have hr : (r : Real) = x ^ D := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, inv_mul_cancel₀ hDreal, Real.rpow_one]
  have hx : 4 ≤ x := by
    have hb : 4 ^ D ≤ r := (polynomialPartitionThreshold_four_pow (by omega : 1 ≤ k + 1)).trans hthreshold.le
    have h : (4 : Real) ^ D ≤ x ^ D := by rw [← hr]; exact_mod_cast hb
    exact le_of_pow_le_pow_left₀ hDpos.ne' hx0 h
  have hthresholdReal : 2 * ((polynomialPartitionThreshold k : Real) + 1) ≤ x ^ (2 * K) := by
    have hb := (polynomialPartitionThreshold_degree_budget hk).trans hthreshold.le
    have hpow : (2 * ((polynomialPartitionThreshold k : Real) + 1)) ^ E ≤
        (x ^ (2 * K)) ^ E := by
      have hexp : (2 * K) * E = D := by rw [hD]; ring
      rw [← pow_mul, hexp, ← hr]
      exact_mod_cast hb
    exact le_of_pow_le_pow_left₀ hE.ne' (by positivity) hpow
  exact polynomial_degree_scale_real K D (k + 1) (polynomialPartitionThreshold k) r v x
    (((k + 1 : Nat) : Real) * (2 : Real) ^ (k + 1 + 1))⁻¹
    hK hD8 hx hr hv hthresholdReal hgamma

/-- Strong diameter control for every positive polynomial degree. -/
theorem strongPolynomialPartitionAt_holds (k : Nat) (hk : 1 ≤ k) :
    StrongPolynomialPartitionAt k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst k
      exact strongPolynomialPartitionAt_one
    · have hk1 : 1 ≤ k := by omega
      intro N r v _ phi hphi hthreshold hrN hv hvupper
      obtain ⟨u, hu, hu4, hscale⟩ := polynomial_degree_scale_exists hk1 hthreshold hvupper
      exact section5_strong_partition_degree_step hk1 (ih hk1) N r v u phi hphi
        hthreshold hrN hv hu hu4 hscale

/-- The stronger diameter estimate proved by the degree induction. -/
theorem corollary_5_6_strong_diameter_holds : corollary_5_6_strong_diameter :=
  corollary_5_6_strong_diameter_iff.mpr strongPolynomialPartitionAt_holds

/-- Corollary 5.6, with the explicit recurrence-supported threshold. -/
theorem corollary_5_6_holds : corollary_5_6 :=
  corollary_5_6_holds_of_strong_diameter corollary_5_6_strong_diameter_holds

/-- Corollary 5.7: remove a polynomial phase on each target-length cell. -/
theorem corollary_5_7_holds : corollary_5_7 :=
  corollary_5_7_holds_of_corollary_5_6 corollary_5_6_holds

/-- The explicitly scale-qualified repair of Corollary 5.8. This is not a
proof of the catalogue statement without its missing scale hypothesis. -/
theorem corollary_5_8_with_scale_holds : corollary_5_8_with_scale :=
  corollary_5_8_with_scale_holds_of_corollary_5_6 corollary_5_6_holds

/-- Lemma 5.9: simultaneous target-length polynomial partitioning. -/
theorem lemma_5_9_holds : lemma_5_9 :=
  lemma_5_9_holds_of_strong_diameter_and_scale_schedule
    corollary_5_6_strong_diameter_holds lemma_5_9_scale_schedule_holds

/-- Lemma 5.14: global phase removal over an input progression partition. -/
theorem lemma_5_14_holds : lemma_5_14 :=
  lemma_5_14_holds_of_corollary_5_6 corollary_5_6_holds

end LeanProofs.GowersSzemeredi
