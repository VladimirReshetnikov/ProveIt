import Surreal.Algebra.Polynomial
import Mathlib.Tactic

/-!
# Algebraization and root counts for finite Laurent sums

The finite algebra behind `trigonometry:thm:polyroots` and
`trigonometry:eq:algebraization`: multiplying a Laurent sum with frequencies
in `[-N,N]` by `U^N` produces an ordinary polynomial of degree at most `2N`.
Roots and their multiplicities here are Mathlib's native polynomial notions;
the analytic angular-coordinate bridge is a separate obligation.
-/

namespace Surreal.LaurentAlgebraization

open Polynomial Finset

noncomputable section

variable {K : Type*}

section Semiring

variable [Semiring K]

/-- The polynomial obtained by clearing the negative powers in a bounded Laurent sum. -/
def polynomial (N : ℕ) (c : ℤ → K) : K[X] :=
  ∑ k ∈ Icc (-(N : ℤ)) N, monomial (k + N).toNat (c k)

/-- Every coefficient inside the shifted window is exactly its original Laurent coefficient. -/
theorem coeff_polynomial (N : ℕ) (c : ℤ → K) (j : ℕ) :
    (polynomial N c).coeff j = if j ≤ 2 * N then c ((j : ℤ) - N) else 0 := by
  classical
  rw [polynomial, finsetSum_coeff]
  by_cases hj : j ≤ 2 * N
  · rw [if_pos hj, sum_eq_single_of_mem ((j : ℤ) - N) (mem_Icc.mpr (by omega))]
    · rw [coeff_monomial]
      simp
    · intro k hk hne
      rw [coeff_monomial, if_neg]
      have hb := mem_Icc.mp hk
      omega
  · rw [if_neg hj]
    apply sum_eq_zero
    intro k hk
    rw [coeff_monomial, if_neg]
    have hb := mem_Icc.mp hk
    omega

/-- The lower endpoint is the constant coefficient after clearing denominators. -/
@[simp] theorem coeff_zero (N : ℕ) (c : ℤ → K) :
    (polynomial N c).coeff 0 = c (-(N : ℤ)) := by simp [coeff_polynomial]

/-- The upper endpoint is the coefficient in degree `2N`. -/
@[simp] theorem coeff_top (N : ℕ) (c : ℤ → K) :
    (polynomial N c).coeff (2 * N) = c (N : ℤ) := by
  rw [coeff_polynomial, if_pos le_rfl]
  congr 1
  omega

/-- Clearing denominators introduces no degrees above twice the frequency bound. -/
theorem natDegree_le (N : ℕ) (c : ℤ → K) : (polynomial N c).natDegree ≤ 2 * N := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  rw [coeff_polynomial, if_neg (not_le_of_gt hj)]

/-- A nonzero top Fourier coefficient makes the degree bound exact. -/
theorem natDegree_eq (N : ℕ) (c : ℤ → K) (hc : c (N : ℤ) ≠ 0) :
    (polynomial N c).natDegree = 2 * N :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le N c) (by simpa using hc)

/-- The cleared polynomial vanishes identically exactly when every coefficient in the window does. -/
theorem polynomial_eq_zero_iff (N : ℕ) (c : ℤ → K) :
    polynomial N c = 0 ↔ ∀ k ∈ Icc (-(N : ℤ)) N, c k = 0 := by
  classical
  constructor
  · intro hp k hk
    have hb := mem_Icc.mp hk
    have he := congrArg (fun P : K[X] => P.coeff (k + N).toNat) hp
    rw [coeff_polynomial, if_pos (by omega), Polynomial.coeff_zero] at he
    convert he using 1
    congr 1
    omega
  · intro hc
    unfold polynomial
    exact sum_eq_zero fun k hk => by rw [hc k hk, map_zero]

end Semiring

section Field

variable [Field K]

local instance : DecidableEq K := Classical.decEq K

/-- The cleared polynomial evaluates to the Laurent sum times its nonzero denominator. -/
theorem eval_polynomial (N : ℕ) (c : ℤ → K) (u : K) (hu : u ≠ 0) :
    (polynomial N c).eval u = u ^ N * ∑ k ∈ Icc (-(N : ℤ)) N, c k * u ^ k := by
  classical
  rw [polynomial, eval_finsetSum, mul_sum]
  apply sum_congr rfl
  intro k hk
  have hb := mem_Icc.mp hk
  have he : u ^ (k + N).toNat = u ^ k * u ^ N := by
    rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_add₀ hu, zpow_natCast]
  rw [eval_monomial, he]
  ring

/-- At every nonzero point, the cleared polynomial and Laurent sum have exactly the same zeros. -/
theorem isRoot_iff (N : ℕ) (c : ℤ → K) (u : K) (hu : u ≠ 0) :
    (polynomial N c).IsRoot u ↔ ∑ k ∈ Icc (-(N : ℤ)) N, c k * u ^ k = 0 := by
  rw [Polynomial.IsRoot, eval_polynomial N c u hu, mul_eq_zero]
  simp only [pow_ne_zero N hu, false_or]

/-- The multiset of nonzero polynomial roots retains the native multiplicities. -/
def nonzeroRoots (N : ℕ) (c : ℤ → K) : Multiset K := by
  classical
  exact (polynomial N c).roots.filter (· ≠ 0)

/-- Multiplicity in the nonzero-root multiset is the native polynomial multiplicity. -/
theorem count_nonzeroRoots (N : ℕ) (c : ℤ → K) (u : K) (hu : u ≠ 0) :
    (nonzeroRoots N c).count u = (polynomial N c).rootMultiplicity u := by
  classical
  rw [nonzeroRoots, Multiset.count_filter_of_pos (p := fun x : K => x ≠ 0) hu, Polynomial.count_roots]

/-- A nontrivial Laurent sum has precisely the indicated nonzero roots. -/
theorem mem_nonzeroRoots (N : ℕ) (c : ℤ → K) (hp : polynomial N c ≠ 0) (u : K) :
    u ∈ nonzeroRoots N c ↔ u ≠ 0 ∧ ∑ k ∈ Icc (-(N : ℤ)) N, c k * u ^ k = 0 := by
  classical
  rw [nonzeroRoots, Multiset.mem_filter, Polynomial.mem_roots hp]
  constructor
  · rintro ⟨hr, hu⟩
    exact ⟨hu, (isRoot_iff N c u hu).mp hr⟩
  · rintro ⟨hu, hr⟩
    exact ⟨(isRoot_iff N c u hu).mpr hr, hu⟩

/-- The total number of nonzero roots counted with multiplicity is at most `2N`. -/
theorem card_nonzeroRoots_le (N : ℕ) (c : ℤ → K) : (nonzeroRoots N c).card ≤ 2 * N := by
  classical
  exact (Multiset.card_le_card (Multiset.filter_le _ _)).trans
    ((Polynomial.card_roots' _).trans (natDegree_le N c))

/-- Over an algebraically closed field, only the multiplicity at zero is lost. -/
theorem card_nonzeroRoots_exact [IsAlgClosed K] (N : ℕ) (c : ℤ → K) :
    (nonzeroRoots N c).card =
      (polynomial N c).natDegree - (polynomial N c).rootMultiplicity 0 := by
  classical
  have he := congrArg Multiset.card
    (Multiset.filter_add_not (fun x : K => x = 0) (polynomial N c).roots)
  rw [Multiset.card_add] at he
  have hz : ((polynomial N c).roots.filter (fun x => x = 0)).card =
      (polynomial N c).rootMultiplicity 0 := by
    rw [← Polynomial.count_roots, Multiset.count_eq_card_filter_eq]
    congr 2
    funext x
    exact propext eq_comm
  rw [hz, FinitePolynomial.roots_card] at he
  change _ + (nonzeroRoots N c).card = _ at he
  omega

/-- A nonzero lower endpoint coefficient excludes zero as a polynomial root. -/
theorem zero_not_mem_roots (N : ℕ) (c : ℤ → K) (hc : c (-(N : ℤ)) ≠ 0) :
    (0 : K) ∉ (polynomial N c).roots := by
  intro hz
  have he := Polynomial.isRoot_of_mem_roots hz
  rw [Polynomial.IsRoot, ← coeff_zero_eq_eval_zero, coeff_zero] at he
  exact hc he

/-- When both endpoints are nonzero, algebraic closedness gives exactly `2N` nonzero roots. -/
theorem card_nonzeroRoots_eq [IsAlgClosed K] (N : ℕ) (c : ℤ → K)
    (hlo : c (-(N : ℤ)) ≠ 0) (hhi : c (N : ℤ) ≠ 0) :
    (nonzeroRoots N c).card = 2 * N := by
  classical
  have hf : (polynomial N c).roots.filter (· ≠ 0) = (polynomial N c).roots := by
    apply Multiset.filter_eq_self.mpr
    intro a ha hz
    exact zero_not_mem_roots N c hlo (hz ▸ ha)
  rw [nonzeroRoots, hf, FinitePolynomial.roots_card, natDegree_eq N c hhi]

end Field
end
end Surreal.LaurentAlgebraization
