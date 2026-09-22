import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.Data.Multiset.Fintype
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring

/-!
# Vieta coefficients and finite Newton identities

This file formalizes the coefficient formula and Newton identities
`polynomial:eq:newton1` and `polynomial:eq:newton2` in
`docs/surcomplex/polynomial-algebra/article.tex`.

Root lists are multisets, so repeated roots retain their multiplicities.
The proof evaluates Mathlib's universal symmetric-polynomial identities
on the finite type of occurrences of that multiset. All sums are finite;
no evaluation of an infinite Laurent expansion is required.
-/

namespace Surreal.FinitePolynomial

noncomputable section

open Polynomial

section CommRing

variable {R : Type*} [CommRing R]

local instance polynomialNewtonDecidableEq : DecidableEq R := Classical.decEq R

/-- The power sum of a finite multiset of roots, counted with multiplicity. -/
def rootPowerSum (s : Multiset R) (k : ℕ) : R :=
  (s.map fun a => a ^ k).sum

/-- With no roots every power sum is zero, including the degree-zero
boundary of the second Newton identity. -/
@[simp] theorem rootPowerSum_empty (k : ℕ) : rootPowerSum (0 : Multiset R) k = 0 := by
  simp [rootPowerSum]

/-- The signed elementary symmetric coefficient in Vieta's formula. -/
def vietaCoefficient (s : Multiset R) (k : ℕ) : R :=
  (-1) ^ k * s.esymm k

@[simp] theorem vietaCoefficient_zero (s : Multiset R) : vietaCoefficient s 0 = 1 := by
  simp [vietaCoefficient, Multiset.esymm]

/-- Elementary symmetric coefficients above the number of roots vanish. -/
theorem vietaCoefficient_eq_zero_of_card_lt (s : Multiset R) {k : ℕ} (hk : s.card < k) :
    vietaCoefficient s k = 0 := by
  simp [vietaCoefficient, Multiset.esymm, Multiset.powersetCard_eq_empty k hk]

/-- Vieta's coefficient identity for a chosen finite product of linear
factors, over any commutative coefficient ring. -/
theorem vieta_prod_coefficient (s : Multiset R) {k : ℕ} (hk : k ≤ s.card) :
    (s.map fun a => X - C a).prod.coeff (s.card - k) = vietaCoefficient s k := by
  rw [Multiset.prod_X_sub_C_coeff s (Nat.sub_le _ _), Nat.sub_sub_self hk]
  rfl

private theorem aeval_esymm_roots (s : Multiset R) (k : ℕ) :
    MvPolynomial.aeval (fun a : s => (a : R)) (MvPolynomial.esymm s R k) = s.esymm k := by
  classical
  simp [MvPolynomial.aeval_esymm_eq_multiset_esymm]

private theorem aeval_psum_roots (s : Multiset R) (k : ℕ) :
    MvPolynomial.aeval (fun a : s => (a : R)) (MvPolynomial.psum s R k) = rootPowerSum s k := by
  classical
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X]
  exact congrArg Multiset.sum (Multiset.map_univ s (fun a : R => a ^ k))

/-- A single finite recurrence underlying both displayed Newton
identities. It includes `k = 0` as the equality `0 = 0`. -/
theorem newton_multiset_uniform (s : Multiset R) (k : ℕ) :
    (k : R) * vietaCoefficient s k +
      ∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i) = 0 := by
  classical
  have h := congrArg (MvPolynomial.aeval (fun a : s => (a : R)))
    (MvPolynomial.mul_esymm_eq_sum s R k)
  simp only [map_mul, map_natCast, map_pow, map_neg, map_one, map_sum,
    aeval_esymm_roots, aeval_psum_roots] at h
  have hsum : (∑ b ∈ (Finset.antidiagonal k).filter (fun b => b.1 < k),
      (-1 : R) ^ b.1 * s.esymm b.1 * rootPowerSum s b.2) =
      ∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i) := by
    rw [Finset.sum_filter, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ]
    simp only [lt_self_iff_false, if_false, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
    rfl
  rw [hsum] at h
  have hsign : (-1 : R) ^ k * (-1) ^ k = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc
    _ = (-1 : R) ^ k * ((k : R) * s.esymm k) +
        ∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i) := by
      unfold vietaCoefficient
      ring
    _ = (-1 : R) ^ k * ((-1) ^ (k + 1) *
        ∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i)) +
        ∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i) := by rw [h]
    _ = ((-1 : R) ^ k * (-1) ^ k) *
        (-(∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i))) +
        ∑ i ∈ Finset.range k, vietaCoefficient s i * rootPowerSum s (k - i) := by
      rw [pow_succ]
      ring
    _ = 0 := by rw [hsign]; simp

/-- Newton's identity with its initial power sum separated out. When
`k` does not exceed the root count, this is `polynomial:eq:newton1`. -/
theorem newton_multiset (s : Multiset R) {k : ℕ} (hk : 0 < k) :
    rootPowerSum s k +
      (∑ i ∈ Finset.Ico 1 k, vietaCoefficient s i * rootPowerSum s (k - i)) +
        (k : R) * vietaCoefficient s k = 0 := by
  have h := newton_multiset_uniform s k
  rw [Finset.sum_range_eq_add_Ico _ hk] at h
  simpa only [vietaCoefficient_zero, Nat.sub_zero, one_mul, add_comm,
    add_left_comm, add_assoc] using h

/-- Above the root count, the last nonzero coefficient is the constant
coefficient; all later elementary symmetric coefficients vanish. This is
the multiset form of `polynomial:eq:newton2`, including an empty root multiset. -/
theorem newton_multiset_above_card (s : Multiset R) {k : ℕ} (hk : s.card < k) :
    rootPowerSum s k +
      ∑ i ∈ Finset.Icc 1 s.card, vietaCoefficient s i * rootPowerSum s (k - i) = 0 := by
  have h := newton_multiset s ((Nat.zero_le s.card).trans_lt hk)
  rw [vietaCoefficient_eq_zero_of_card_lt s hk, mul_zero, add_zero] at h
  have hsum : (∑ i ∈ Finset.Icc 1 s.card,
      vietaCoefficient s i * rootPowerSum s (k - i)) =
      ∑ i ∈ Finset.Ico 1 k, vietaCoefficient s i * rootPowerSum s (k - i) := by
    apply Finset.sum_subset
    · intro i hi
      exact Finset.mem_Ico.mpr ⟨(Finset.mem_Icc.mp hi).1,
        (Finset.mem_Icc.mp hi).2.trans_lt hk⟩
    · intro i hi hni
      have hci : s.card < i := lt_of_not_ge fun hle =>
        hni (Finset.mem_Icc.mpr ⟨(Finset.mem_Ico.mp hi).1, hle⟩)
      rw [vietaCoefficient_eq_zero_of_card_lt s hci, zero_mul]
  rw [hsum]
  exact h

end CommRing

section Field

variable {K : Type*} [Field K]

/-- The Vieta coefficient identity preceding `polynomial:eq:newton1`
for a monic split polynomial, with its roots counted with multiplicity. -/
theorem vieta_coefficient (p : K[X]) (hp : p.Monic) (hs : p.Splits)
    {k : ℕ} (hk : k ≤ p.natDegree) :
    p.coeff (p.natDegree - k) = vietaCoefficient p.roots k := by
  rw [Polynomial.coeff_eq_esymm_roots_of_splits hs (Nat.sub_le _ _),
    hp.leadingCoeff, one_mul, Nat.sub_sub_self hk]
  rfl

/-- `polynomial:eq:newton1`: for `1 ≤ k ≤ n`, the final term is `k cₖ`.
There is no division by `k`, so the identity is valid in any characteristic. -/
theorem newton_identity_le_degree (p : K[X]) (hp : p.Monic) (hs : p.Splits)
    {k : ℕ} (hk0 : 0 < k) (hkn : k ≤ p.natDegree) :
    rootPowerSum p.roots k +
      (∑ i ∈ Finset.Ico 1 k, p.coeff (p.natDegree - i) * rootPowerSum p.roots (k - i)) +
        (k : K) * p.coeff (p.natDegree - k) = 0 := by
  rw [vieta_coefficient p hp hs hkn]
  have hsum : (∑ i ∈ Finset.Ico 1 k,
      p.coeff (p.natDegree - i) * rootPowerSum p.roots (k - i)) =
      ∑ i ∈ Finset.Ico 1 k, vietaCoefficient p.roots i * rootPowerSum p.roots (k - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [vieta_coefficient p hp hs ((Finset.mem_Ico.mp hi).2.le.trans hkn)]
  rw [hsum]
  exact newton_multiset p.roots hk0

/-- `polynomial:eq:newton2`: for `k > n`, the finite recurrence stops at
the constant coefficient. For `n = 0` a monic polynomial is one, and both
the root multiset and displayed sum are empty. -/
theorem newton_identity_gt_degree (p : K[X]) (hp : p.Monic) (hs : p.Splits)
    {k : ℕ} (hk : p.natDegree < k) :
    rootPowerSum p.roots k +
      ∑ i ∈ Finset.Icc 1 p.natDegree,
        p.coeff (p.natDegree - i) * rootPowerSum p.roots (k - i) = 0 := by
  have hcard : p.roots.card = p.natDegree := hs.natDegree_eq_card_roots.symm
  have h := newton_multiset_above_card p.roots (hcard ▸ hk)
  rw [hcard] at h
  have hsum : (∑ i ∈ Finset.Icc 1 p.natDegree,
      p.coeff (p.natDegree - i) * rootPowerSum p.roots (k - i)) =
      ∑ i ∈ Finset.Icc 1 p.natDegree,
        vietaCoefficient p.roots i * rootPowerSum p.roots (k - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [vieta_coefficient p hp hs (Finset.mem_Icc.mp hi).2]
  rw [hsum]
  exact h

end Field

end

end Surreal.FinitePolynomial
