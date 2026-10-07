import Mathlib.Analysis.SpecialFunctions.Exp
import OAI.Combinatorics.Progressions.Dynamics.UnconditionedWidthExponentialBudget
import OAI.Combinatorics.Progressions.Lattices.ComparableScalarPrimeParameters

namespace OAI

section

namespace Erdos3

theorem exists_unconditioned_prime_sides (n₀ : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    ∃ P : Fin n₀ → ℕ, (∀ i, (P i).Prime) ∧ Function.Injective P ∧
      (∀ i j, P i ≤ 2 ^ (n₀ + 1) * P j) ∧
      ∀ i, Real.exp p ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (p + (n₀ : ℝ) + 2) := by
  let t := ⌈Real.exp p⌉₊
  have hceil : Real.exp p ≤ (t : ℝ) := Nat.le_ceil _
  have ht : 0 < t := by exact_mod_cast (Real.exp_pos p).trans_le hceil
  have he1 : (1 : ℝ) ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have htR : (t : ℝ) ≤ Real.exp (p + 1) := by
    calc
      _ ≤ Real.exp p + 1 := (Nat.ceil_lt_add_one (Real.exp_nonneg p)).le
      _ ≤ Real.exp p * 2 := by linarith
      _ ≤ Real.exp p * Real.exp 1 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg p)
      _ = Real.exp (p + 1) := (Real.exp_add p 1).symm
  have hpow : (2 : ℝ) ^ n₀ ≤ Real.exp (n₀ : ℝ) := by
    calc
      _ ≤ (Real.exp 1) ^ n₀ := pow_le_pow_left₀ (by norm_num) htwo n₀
      _ = _ := by rw [← Real.exp_nat_mul, mul_one]
  obtain ⟨P, hmono, hP⟩ := exists_distinct_primes_dyadic n₀ t ht
  have hlow (i : Fin n₀) : t < P i :=
    (Nat.le_mul_of_pos_left t (by positivity : 0 < 2 ^ i.val)).trans_lt (hP i).2.1
  have hhigh (i : Fin n₀) : P i ≤ 2 ^ n₀ * t :=
    (hP i).2.2.trans (Nat.mul_le_mul_right t
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt i.isLt)))
  refine ⟨P, fun i => (hP i).1, hmono.injective, ?_, ?_⟩
  · intro i j
    exact (hhigh i).trans (Nat.mul_le_mul
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.le_succ n₀)) (hlow j).le)
  · intro i
    refine ⟨hceil.trans (Nat.cast_le.mpr (hlow i).le), ?_⟩
    calc
      (P i : ℝ) ≤ (2 : ℝ) ^ n₀ * (t : ℝ) := by exact_mod_cast hhigh i
      _ ≤ Real.exp (n₀ : ℝ) * Real.exp (p + 1) :=
        mul_le_mul hpow htR (Nat.cast_nonneg t) (Real.exp_nonneg _)
      _ = Real.exp ((n₀ : ℝ) + (p + 1)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp (p + (n₀ : ℝ) + 2) := Real.exp_le_exp.mpr (by linarith)

theorem exists_unconditioned_prime_side_budget (n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ p : ℝ, 2 ≤ p →
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ i, (P i).Prime),
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ i, Real.exp p ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (p + (n₀ : ℝ) + 2)) ∧
        ∀ d : ℕ, (d : ℝ) ≤ p →
          let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
          unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
            (unconditionedSpatialTrimFraction d (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((p + 2) ^ E) := by
  obtain ⟨E, hE, hbudget⟩ := exists_unconditionedSpatialWidthCutoff_exp_budget n₀
  refine ⟨E, hE, ?_⟩
  intro p hp
  obtain ⟨P, hprime, hinj, hcompare, hrange⟩ :=
    exists_unconditioned_prime_sides n₀ (by linarith : 0 ≤ p)
  refine ⟨P, hprime, hinj, hcompare, hrange, ?_⟩
  intro d hd
  let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
  exact hbudget p hp d hd P (fun i => (hrange i).2)

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem unconditionedSpatialWidthCutoff_antitone_surplus
    {K : Type*} [Fintype K] [DecidableEq K] (P : K → ℕ) [∀ k, NeZero (P k)]
    (d : ℕ) {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ : σ₁ ≤ σ₂) :
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d σ₂) (unconditionedCollisionWidth P σ₂) ≤
    unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction d σ₁) (unconditionedCollisionWidth P σ₁) := by
  have htrim : unconditionedSpatialTrimFraction d σ₁ ≤ unconditionedSpatialTrimFraction d σ₂ :=
    div_le_div_of_nonneg_right hσ (by positivity)
  have htrimpos : 0 < unconditionedSpatialTrimFraction d σ₁ := by
    unfold unconditionedSpatialTrimFraction
    positivity
  have hcollision : unconditionedCollisionWidth P σ₂ ≤ unconditionedCollisionWidth P σ₁ :=
    div_le_div_of_nonneg_left (by positivity) hσ₁ hσ
  have hsite : 0 ≤ unconditionedResidueSiteBound P :=
    Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  unfold unconditionedSpatialWidthCutoff
  apply max_le_max
  · exact div_le_div_of_nonneg_left (by norm_num) htrimpos htrim
  · apply (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (max_le_max_left _ hcollision) (by positivity))
      (htrimpos.le.trans htrim)).trans
    exact div_le_div_of_nonneg_left (by positivity) htrimpos htrim

theorem exists_unconditioned_late_prime_side_budget (n₀ : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (p t : ℝ), 2 ≤ p → p ≤ t →
      ∃ (P : Fin n₀ → ℕ) (hprime : ∀ i, (P i).Prime),
        Function.Injective P ∧ (∀ i j, P i ≤ 2 ^ (n₀ + 1) * P j) ∧
        (∀ i, Real.exp t ≤ (P i : ℝ) ∧ (P i : ℝ) ≤ Real.exp (t + (n₀ : ℝ) + 2)) ∧
        (∀ i, Real.exp p ≤ (P i : ℝ)) ∧
        ∀ d : ℕ, (d : ℝ) ≤ p →
          let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
          unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
            (unconditionedSpatialTrimFraction d (Real.exp (-p)))
            (unconditionedCollisionWidth P (Real.exp (-p))) ≤ Real.exp ((t + 2) ^ E) := by
  obtain ⟨E, hE, hbudget⟩ := exists_unconditioned_prime_side_budget n₀
  refine ⟨E, hE, ?_⟩
  intro p t hp hpt
  obtain ⟨P, hprime, hinj, hcompare, hrange, hwidth⟩ := hbudget t (hp.trans hpt)
  refine ⟨P, hprime, hinj, hcompare, hrange,
    fun i => (Real.exp_le_exp.mpr hpt).trans (hrange i).1, ?_⟩
  intro d hd
  let : ∀ i, NeZero (P i) := fun i => ⟨(hprime i).ne_zero⟩
  exact (unconditionedSpatialWidthCutoff_antitone_surplus P d (Real.exp_pos (-t))
    (Real.exp_le_exp.mpr (neg_le_neg hpt))).trans (hwidth d (hd.trans hpt))

end Erdos3

end

end OAI
