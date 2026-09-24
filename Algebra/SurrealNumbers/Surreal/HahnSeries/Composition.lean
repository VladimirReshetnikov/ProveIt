import Surreal.HahnSeries.Evaluation
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
# Composition under admissible Hahn evaluation

This proves the univariate composition clause of `a:cor:complexsub`:
evaluating `A(B(X))` at a positive-order Hahn series agrees with first
evaluating `B`, then evaluating `A` at the result, when `B(0) = 0`.
Both formal series are arbitrary and the zero inner series is included.

The proof is coefficientwise. At a fixed Hahn exponent only finitely many
powers of the original argument contribute. For each such power, formal
substitution has only finitely many contributing outer coefficients.
These two finiteness facts justify the interchange; separate existence of
two iterated Hahn sums is not used as a summability criterion. No topology,
derivative compatibility, or multivariable substitution is asserted here.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R : Type*} [AddCommMonoid Γ] [LinearOrder Γ]
  [IsOrderedCancelAddMonoid Γ] [CommRing R]

/-- Every admissible formal evaluation has nonnegative Hahn order. -/
theorem orderTop_evaluate_nonneg (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (F : PowerSeries R) : 0 ≤ (evaluate x hx F).orderTop := by
  apply le_orderTop_iff_forall.mpr
  intro g hg
  rw [coeff_evaluate]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  rw [single_zero_mul_eq_smul, coeff_smul]
  have hpow : 0 ≤ (x ^ n).orderTop :=
    (nsmul_nonneg hx.le n).trans orderTop_nsmul_le_orderTop_pow
  rw [coeff_eq_zero_of_lt_orderTop (hg.trans_le hpow), smul_zero]

/-- A formal series with zero constant coefficient evaluates to positive
Hahn order. This supplies admissibility for the inner substitution in
`a:cor:complexsub`, including when its value is zero. -/
theorem orderTop_evaluate_pos_of_constantCoeff_zero (x : R⟦Γ⟧)
    (hx : 0 < x.orderTop) (B : PowerSeries R) (hB : B.constantCoeff = 0) :
    0 < (evaluate x hx B).orderTop := by
  have hc : (evaluate x hx B).coeff 0 = 0 := (coeff_zero_evaluate x hx B).trans hB
  exact lt_of_le_of_ne (orderTop_evaluate_nonneg x hx B)
    (orderTop_ne_of_coeff_eq_zero hc).symm

/-- A finite set containing all powers contributing at a Hahn exponent
computes that coefficient of every formal evaluation. The set is independent
of the formal coefficient sequence. -/
theorem coeff_evaluate_eq_sum (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (F : PowerSeries R) (g : Γ) (s : Finset ℕ)
    (hs : ∀ n ∉ s, (x ^ n).coeff g = 0) :
    (evaluate x hx F).coeff g = ∑ n ∈ s, F.coeff n * (x ^ n).coeff g := by
  rw [coeff_evaluate]
  simp only [single_zero_mul_eq_smul, coeff_smul, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro n hn
  by_contra hns
  exact hn (by simp only [hs n hns, mul_zero])

/-- The full univariate composition identity from `a:cor:complexsub`.
The inner admissibility proof is supplied by the zero constant coefficient;
neither formal series has a coefficient-growth restriction. -/
theorem evaluate_subst (x : R⟦Γ⟧) (hx : 0 < x.orderTop)
    (A B : PowerSeries R) (hB : B.constantCoeff = 0) :
    evaluate x hx (A.subst B) =
      evaluate (evaluate x hx B) (orderTop_evaluate_pos_of_constantCoeff_zero x hx B hB) A := by
  classical
  apply _root_.HahnSeries.ext
  funext g
  let s := (SummableFamily.pow_finite_co_support hx g).toFinset
  have hs : ∀ n ∉ s, (x ^ n).coeff g = 0 := by
    intro n hn
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] using hn
  have heval (F : PowerSeries R) :
      (evaluate x hx F).coeff g = ∑ k ∈ s, F.coeff k * (x ^ k).coeff g :=
    coeff_evaluate_eq_sum x hx F g s hs
  have hsubst : PowerSeries.HasSubst B := PowerSeries.HasSubst.of_constantCoeff_zero' hB
  have hfinite (k : ℕ) :
      (fun n => A.coeff n * (B ^ n).coeff k).HasFiniteSupport := by
    simpa only [smul_eq_mul] using PowerSeries.coeff_subst_finite' hsubst A k
  have hfinite_mul (k : ℕ) :
      (fun n => (A.coeff n * (B ^ n).coeff k) * (x ^ k).coeff g).HasFiniteSupport :=
    (hfinite k).mul_left (fun _ => (x ^ k).coeff g)
  calc
    (evaluate x hx (A.subst B)).coeff g =
        ∑ k ∈ s, (∑ᶠ n, A.coeff n * (B ^ n).coeff k) * (x ^ k).coeff g := by
      rw [heval]
      simp only [PowerSeries.coeff_subst' hsubst, smul_eq_mul]
    _ = ∑ k ∈ s, ∑ᶠ n, (A.coeff n * (B ^ n).coeff k) * (x ^ k).coeff g := by
      apply Finset.sum_congr rfl
      intro k _
      exact finsum_mul' _ _ (hfinite k)
    _ = ∑ᶠ n, ∑ k ∈ s, (A.coeff n * (B ^ n).coeff k) * (x ^ k).coeff g :=
      sum_finsum_comm s _ (fun k _ => hfinite_mul k)
    _ = ∑ᶠ n, A.coeff n * ((evaluate x hx B) ^ n).coeff g := by
      apply finsum_congr
      intro n
      simp only [mul_assoc, ← Finset.mul_sum, ← heval, map_pow]
    _ = (evaluate (evaluate x hx B)
        (orderTop_evaluate_pos_of_constantCoeff_zero x hx B hB) A).coeff g := by
      rw [coeff_evaluate]
      simp only [single_zero_mul_eq_smul, coeff_smul, smul_eq_mul]

end
end Surreal.HahnSeries
