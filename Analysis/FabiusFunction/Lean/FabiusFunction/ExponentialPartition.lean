import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Finset.Finsupp
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exponential coefficients from weighted partitions

This module develops the finite combinatorics of the exponential formula.
A weighted partition of `n` is represented by a finitely supported
multiplicity vector, and `partitionExpSum E n` sums the corresponding
monomials with reciprocal-factorial weights.

The construction works over every commutative rational algebra.  Factorial
inverses are taken in `ℚ` and then act by scalars, so neither a field
structure nor cancellation in the target is required.  The marked-part
bijection gives the universal recurrence for coefficients of
`exp (∑ j ≥ 1, E j X^j)`.  The companion module
`FabiusFunction.ExponentialBell` identifies this finite partition sum with
the recursive saddle coefficient `SaddleExpansion.expCoeff`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

noncomputable def weightedPartitions (n : ℕ) : Finset (ℕ →₀ ℕ) :=
  ((Icc 1 n).finsupp (fun _ => range (n + 1))).filter
    (fun f => ∑ j ∈ Icc 1 n, j * f j = n)

/-- Membership in `weightedPartitions n`, unfolded: support inside
`[1, n]`, multiplicities at most `n`, and total weight `n`. -/
theorem mem_weightedPartitions {n : ℕ} {f : ℕ →₀ ℕ} :
    f ∈ weightedPartitions n ↔
      f.support ⊆ Icc 1 n ∧ (∀ j ∈ Icc 1 n, f j ≤ n) ∧
        ∑ j ∈ Icc 1 n, j * f j = n := by
  simp only [weightedPartitions, Finset.mem_filter, Finset.mem_finsupp_iff,
    Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun j hj => by have := h2 j hj; omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, fun j hj => by have := h2 j hj; omega⟩, h3⟩

/-- Membership from support and weight alone: the multiplicity bound is
automatic. -/
theorem mem_weightedPartitions_of {n : ℕ} {f : ℕ →₀ ℕ}
    (hsupp : f.support ⊆ Icc 1 n)
    (hweight : ∑ j ∈ Icc 1 n, j * f j = n) :
    f ∈ weightedPartitions n := by
  refine mem_weightedPartitions.mpr ⟨hsupp, fun j hj => ?_, hweight⟩
  have hj' := Finset.mem_Icc.mp hj
  have hle : j * f j ≤ n := by
    rw [← hweight]
    exact Finset.single_le_sum (f := fun k => k * f k)
      (fun k _ => Nat.zero_le _) hj
  nlinarith [hj'.1]

/-- The weighted partition sum
`P(n) = ∑_λ ∏ⱼ (mⱼ!)⁻¹ • Eⱼ^{mⱼ}` of a coefficient sequence `E`.

The reciprocal factorials live in `ℚ` and act by scalars.  Consequently
the definition works in every commutative rational algebra, including rings
with zero divisors. -/
noncomputable def partitionExpSum {R : Type*} [CommRing R] [Algebra ℚ R]
    (E : ℕ → R) (n : ℕ) : R :=
  ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
    (((f j).factorial : ℚ)⁻¹) • E j ^ f j

/-- The only weighted partition of `0` is the empty one. -/
@[simp] theorem weightedPartitions_zero :
    weightedPartitions 0 = {0} := by
  ext f
  simp only [mem_weightedPartitions, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, -, -⟩
    ext j
    by_contra hne
    have : j ∈ f.support := Finsupp.mem_support_iff.mpr
      (by simpa using hne)
    have := h1 this
    simp at this
  · rintro rfl
    simp

/-- The partition sum starts at `1`, represented by the empty product. -/
@[simp] theorem partitionExpSum_zero {R : Type*} [CommRing R] [Algebra ℚ R]
    (E : ℕ → R) : partitionExpSum E 0 = 1 := by
  simp [partitionExpSum]

private theorem prod_extend {R : Type*} [CommRing R] [Algebra ℚ R]
    (E : ℕ → R)
    (g : ℕ →₀ ℕ) {M M' : ℕ} (h : M ≤ M') (hsupp : g.support ⊆ Icc 1 M) :
    ∏ k ∈ Icc 1 M', (((g k).factorial : ℚ)⁻¹) • E k ^ g k =
      ∏ k ∈ Icc 1 M, (((g k).factorial : ℚ)⁻¹) • E k ^ g k := by
  symm
  refine Finset.prod_subset (Finset.Icc_subset_Icc_right h) ?_
  intro k _ hk
  have : g k = 0 := by
    by_contra hne
    exact hk (hsupp (Finsupp.mem_support_iff.mpr hne))
  simp [this]

/-- Pointwise values of a multiplicity vector with one `j`-part
removed. -/
private theorem sub_single_apply (f : ℕ →₀ ℕ) (j k : ℕ) :
    (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k =
      f k - (if j = k then 1 else 0) := by
  rw [Finsupp.tsub_apply, Finsupp.single_apply]

/-- **Removing a marked part.**  A weighted partition `f` of `n` that
carries at least one `j`-part, `j ∈ [1, n]`, becomes a weighted
partition of `n - j` once one such part is deleted: the weight drops by
`j`, and the support stays inside `[1, n - j]`. -/
private theorem sub_single_mem {n j : ℕ} {f : ℕ →₀ ℕ}
    (hj : j ∈ Icc 1 n) (hfj : 1 ≤ f j) (hsupp : f.support ⊆ Icc 1 n)
    (hweight : ∑ k ∈ Icc 1 n, k * f k = n) :
    f - (Finsupp.single j 1 : ℕ →₀ ℕ) ∈ weightedPartitions (n - j) := by
  have happly := sub_single_apply f j
  obtain ⟨u, hu⟩ : ∃ u, f j = u + 1 := ⟨f j - 1, by omega⟩
  have hweight' : ∑ k ∈ Icc 1 n,
      k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k = n - j := by
    have hsplit := Finset.add_sum_erase (Icc 1 n) (fun k => k * f k) hj
    have hsplit' := Finset.add_sum_erase (Icc 1 n)
      (fun k => k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k) hj
    have heq : ∀ k ∈ (Icc 1 n).erase j,
        k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k = k * f k := by
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      rw [happly, if_neg (fun h => hkj h.symm), Nat.sub_zero]
    rw [Finset.sum_congr rfl heq] at hsplit'
    have hjval : (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) j = u := by
      rw [happly, if_pos rfl, hu, Nat.add_sub_cancel]
    rw [hjval] at hsplit'
    have hlin : j * f j = j * u + j := by rw [hu]; ring
    rw [hlin] at hsplit
    omega
  refine mem_weightedPartitions_of ?_ ?_
  · intro k hk
    have hk1 : (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k ≠ 0 :=
      Finsupp.mem_support_iff.mp hk
    have hk2 : f k ≠ 0 := by
      intro hzero
      apply hk1
      rw [happly, hzero, Nat.zero_sub]
    have hk3 := Finset.mem_Icc.mp (hsupp (Finsupp.mem_support_iff.mpr hk2))
    have hk4 : k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k ≤ n - j := by
      rw [← hweight']
      exact Finset.single_le_sum
        (f := fun t => t * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) t)
        (fun t _ => Nat.zero_le _) (Finset.mem_Icc.mpr hk3)
    have hk5 : 1 ≤ (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k := by omega
    refine Finset.mem_Icc.mpr ⟨hk3.1, ?_⟩
    nlinarith [hk3.1]
  · have hext : ∑ k ∈ Icc 1 (n - j),
        k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k =
        ∑ k ∈ Icc 1 n, k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k := by
      refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega)) ?_
      intro k hk hknot
      have hk' := Finset.mem_Icc.mp hk
      have hklt : n - j < k := by
        by_contra hcon
        exact hknot (Finset.mem_Icc.mpr ⟨hk'.1, by omega⟩)
      rcases Nat.eq_zero_or_pos
          ((f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k) with hzk | hzk
      · rw [hzk, Nat.mul_zero]
      · exfalso
        have hk4 : k * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k ≤ n - j := by
          rw [← hweight']
          exact Finset.single_le_sum
            (f := fun t => t * (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) t)
            (fun t _ => Nat.zero_le _) hk
        nlinarith
    rw [hext, hweight']

private theorem succ_mul_invFactorial_smul
    {R : Type*} [CommRing R] [Algebra ℚ R] (u : ℕ) (x : R) :
    ((u + 1 : ℕ) : R) *
        ((((u + 1).factorial : ℚ)⁻¹) • x ^ (u + 1)) =
      x * (((u.factorial : ℚ)⁻¹) • x ^ u) := by
  have hrat :
      ((u + 1 : ℕ) : ℚ) * (((u + 1).factorial : ℚ)⁻¹) =
        ((u.factorial : ℚ)⁻¹) := by
    rw [Nat.factorial_succ]
    push_cast
    field_simp
  simp only [Algebra.smul_def]
  rw [show ((u + 1 : ℕ) : R) =
      algebraMap ℚ R ((u + 1 : ℕ) : ℚ) by norm_num,
    ← mul_assoc, ← map_mul, hrat, pow_succ']
  ring

/-- **The exponential-formula recurrence.**  Over any commutative rational
algebra and for any coefficient sequence `E`, the weighted partition sum
obeys `n · P(n) = ∑_{j=1}^n j · Eⱼ · P(n-j)`.

The proof marks one part: `n = ∑ j·mⱼ` distributes the factor `n` over
the parts, and removing a marked `j`-part is a bijection onto the partitions
of `n-j`.  All cancellation takes place in `ℚ` before scalars act on the
target, so the result remains valid in rings with zero divisors. -/
theorem partitionExpSum_recurrence
    {R : Type*} [CommRing R] [Algebra ℚ R] (E : ℕ → R) (n : ℕ) :
    (n : R) * partitionExpSum E n =
      ∑ j ∈ Icc 1 n, (j : R) * E j * partitionExpSum E (n - j) := by
  -- distribute the weight over the parts
  have hstep1 : (n : R) * partitionExpSum E n =
      ∑ j ∈ Icc 1 n, ∑ f ∈ weightedPartitions n,
        ((j : R) * (f j : R)) *
          ∏ k ∈ Icc 1 n,
            (((f k).factorial : ℚ)⁻¹) • E k ^ f k := by
    rw [partitionExpSum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hw := (mem_weightedPartitions.mp hf).2.2
    rw [← Finset.sum_mul]
    congr 1
    have hcast : ((∑ k ∈ Icc 1 n, k * f k : ℕ) : R) =
        ∑ k ∈ Icc 1 n, (k : R) * (f k : R) := by
      push_cast
      rfl
    rw [← hcast, hw]
  rw [hstep1]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_Icc.mp hj
  -- only partitions actually containing a `j`-part contribute
  have hfilter : ∑ f ∈ weightedPartitions n,
      ((j : R) * (f j : R)) * ∏ k ∈ Icc 1 n,
        (((f k).factorial : ℚ)⁻¹) • E k ^ f k =
      ∑ f ∈ (weightedPartitions n).filter (fun f => 1 ≤ f j),
        ((j : R) * (f j : R)) * ∏ k ∈ Icc 1 n,
          (((f k).factorial : ℚ)⁻¹) • E k ^ f k := by
    symm
    refine Finset.sum_filter_of_ne fun f _ hne => ?_
    by_contra hlt
    have : f j = 0 := by omega
    rw [this] at hne
    simp at hne
  rw [hfilter, partitionExpSum, Finset.mul_sum]
  -- remove the marked part: bijection with the partitions of `n - j`
  refine Finset.sum_bij'
    (fun (f : ℕ →₀ ℕ) _ => f - (Finsupp.single j 1 : ℕ →₀ ℕ))
    (fun (g : ℕ →₀ ℕ) _ => g + (Finsupp.single j 1 : ℕ →₀ ℕ))
    ?_ ?_ ?_ ?_ ?_
  · -- forward membership: delete the marked part
    intro f hf
    obtain ⟨hfmem, hfj⟩ := Finset.mem_filter.mp hf
    obtain ⟨hsupp, -, hweight⟩ := mem_weightedPartitions.mp hfmem
    exact sub_single_mem hj hfj hsupp hweight
  · -- backward membership
    intro g hg
    obtain ⟨hsupp, -, hweight⟩ := mem_weightedPartitions.mp hg
    have happly : ∀ k : ℕ, (g + (Finsupp.single j 1 : ℕ →₀ ℕ)) k =
        g k + (if j = k then 1 else 0) := by
      intro k
      rw [Finsupp.add_apply, Finsupp.single_apply]
    refine Finset.mem_filter.mpr ⟨mem_weightedPartitions_of ?_ ?_, ?_⟩
    · intro k hk
      have hk1 : (g + (Finsupp.single j 1 : ℕ →₀ ℕ)) k ≠ 0 :=
        Finsupp.mem_support_iff.mp hk
      rw [happly] at hk1
      by_cases hkj : j = k
      · subst hkj
        exact hj
      · rw [if_neg hkj, Nat.add_zero] at hk1
        have := Finset.mem_Icc.mp (hsupp (Finsupp.mem_support_iff.mpr hk1))
        exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
    · have hgn : ∑ k ∈ Icc 1 n, k * g k = n - j := by
        rw [← hweight]
        symm
        refine Finset.sum_subset (Finset.Icc_subset_Icc_right (by omega)) ?_
        intro k _ hk
        have hzk : g k = 0 := by
          by_contra hne
          exact hk (hsupp (Finsupp.mem_support_iff.mpr hne))
        rw [hzk, Nat.mul_zero]
      have hsplit := Finset.add_sum_erase (Icc 1 n)
        (fun k => k * (g + (Finsupp.single j 1 : ℕ →₀ ℕ)) k) hj
      have heq : ∀ k ∈ (Icc 1 n).erase j,
          k * (g + (Finsupp.single j 1 : ℕ →₀ ℕ)) k = k * g k := by
        intro k hk
        have hkj := (Finset.mem_erase.mp hk).1
        rw [happly, if_neg (fun h => hkj h.symm), Nat.add_zero]
      rw [Finset.sum_congr rfl heq] at hsplit
      have hjval : (g + (Finsupp.single j 1 : ℕ →₀ ℕ)) j = g j + 1 := by
        rw [happly, if_pos rfl]
      rw [hjval] at hsplit
      have hlin : j * (g j + 1) = j * g j + j := by ring
      rw [hlin] at hsplit
      have hgsplit := Finset.add_sum_erase (Icc 1 n) (fun k => k * g k) hj
      omega
    · have hjval : (g + (Finsupp.single j 1 : ℕ →₀ ℕ)) j = g j + 1 := by
        rw [happly, if_pos rfl]
      omega
  · -- left inverse
    intro f hf
    have hfj := (Finset.mem_filter.mp hf).2
    ext k
    rw [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases h : j = k
    · subst h
      rw [if_pos rfl]
      omega
    · rw [if_neg h]
      omega
  · -- right inverse
    intro g _
    ext k
    rw [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
    split_ifs <;> omega
  · -- the terms match
    intro f hf
    obtain ⟨hfmem, hfj⟩ := Finset.mem_filter.mp hf
    obtain ⟨hsupp, -, hweight⟩ := mem_weightedPartitions.mp hfmem
    have happly := sub_single_apply f j
    obtain ⟨u, hu⟩ : ∃ u, f j = u + 1 := ⟨f j - 1, by omega⟩
    have hsupp' : (f - (Finsupp.single j 1 : ℕ →₀ ℕ)).support ⊆
        Icc 1 (n - j) :=
      (mem_weightedPartitions.mp (sub_single_mem hj hfj hsupp hweight)).1
    rw [← prod_extend E (f - (Finsupp.single j 1 : ℕ →₀ ℕ))
      (M := n - j) (M' := n) (by omega) hsupp']
    rw [← Finset.mul_prod_erase (Icc 1 n)
        (fun k => (((f k).factorial : ℚ)⁻¹) • E k ^ f k) hj,
      ← Finset.mul_prod_erase (Icc 1 n)
        (fun k =>
          ((((f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k).factorial : ℚ)⁻¹) •
            E k ^ (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k) hj]
    have herase : ∀ k ∈ (Icc 1 n).erase j,
        ((((f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k).factorial : ℚ)⁻¹) •
            E k ^ (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k =
          (((f k).factorial : ℚ)⁻¹) • E k ^ f k := by
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      rw [happly, if_neg (fun h => hkj h.symm), Nat.sub_zero]
    rw [Finset.prod_congr rfl herase]
    have hjval : (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) j = u := by
      rw [happly, if_pos rfl, hu, Nat.add_sub_cancel]
    rw [hjval, hu]
    have hmarked := succ_mul_invFactorial_smul (R := R) u (E j)
    calc
      ((j : R) * ((u + 1 : ℕ) : R)) *
          (((((u + 1).factorial : ℚ)⁻¹) • E j ^ (u + 1)) *
            ∏ k ∈ (Icc 1 n).erase j,
              (((f k).factorial : ℚ)⁻¹) • E k ^ f k) =
        (j : R) *
          (((u + 1 : ℕ) : R) *
            ((((u + 1).factorial : ℚ)⁻¹) • E j ^ (u + 1))) *
          ∏ k ∈ (Icc 1 n).erase j,
            (((f k).factorial : ℚ)⁻¹) • E k ^ f k := by ring
      _ = (j : R) *
          (E j * (((u.factorial : ℚ)⁻¹) • E j ^ u) *
            ∏ k ∈ (Icc 1 n).erase j,
              (((f k).factorial : ℚ)⁻¹) • E k ^ f k) := by
        rw [hmarked]
        ring
      _ = ((j : R) * E j) *
          ((((u.factorial : ℚ)⁻¹) • E j ^ u) *
            ∏ k ∈ (Icc 1 n).erase j,
              (((f k).factorial : ℚ)⁻¹) • E k ^ f k) := by ring

/-- Normalized successor form of the exponential-formula recurrence.  This
is the coefficient recursion for
`exp (∑ j ≥ 1, E j * X ^ j)`, whose exponent has zero constant term. -/
theorem partitionExpSum_succ
    {R : Type*} [CommRing R] [Algebra ℚ R] (E : ℕ → R) (n : ℕ) :
    partitionExpSum E (n + 1) =
      ((n + 1 : ℚ)⁻¹) •
        ∑ j ∈ range (n + 1),
          (j + 1 : R) * E (j + 1) * partitionExpSum E (n - j) := by
  have hsum :
      (∑ j ∈ Icc 1 (n + 1),
        (j : R) * E j * partitionExpSum E (n + 1 - j)) =
      ∑ j ∈ range (n + 1),
        (j + 1 : R) * E (j + 1) * partitionExpSum E (n - j) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [show 1 + j = j + 1 by omega,
      show n + 1 - (j + 1) = n - j by omega]
    push_cast
    rfl
  rw [← hsum, ← partitionExpSum_recurrence E (n + 1)]
  simp only [Algebra.smul_def]
  rw [show ((n + 1 : ℕ) : R) =
      algebraMap ℚ R (n + 1 : ℚ) by norm_num,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀]
  · rw [map_one, one_mul]
  · exact_mod_cast Nat.succ_ne_zero n

/-- Over a characteristic-zero field, the rational-scalar definition of
`partitionExpSum` is the familiar product of powers divided by
multiplicity factorials. -/
theorem partitionExpSum_eq_sum_div
    {F : Type*} [Field F] [CharZero F] (E : ℕ → F) (n : ℕ) :
    partitionExpSum E n =
      ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
        E j ^ f j / (f j).factorial := by
  unfold partitionExpSum
  apply Finset.sum_congr rfl
  intro f _hf
  apply Finset.prod_congr rfl
  intro j _hj
  simp only [Algebra.smul_def, map_inv₀, map_natCast, div_eq_mul_inv]
  rw [mul_comm]

end Fabius
