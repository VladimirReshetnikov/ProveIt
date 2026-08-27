import FabiusFunction.ThueMorseHessenberg
import Mathlib.Data.Finset.Finsupp

/-!
# The partition and Bell-polynomial formulae for the Thue–Morse sign

Exponentiating the Euler transform writes each sign as a finite sum
over weighted partitions.  We formalize this without any analytic
step: the partition sum obeys the *marked-part recurrence* — the
coefficient recurrence of `exp(∑ xⱼzʲ)` — proved by pure finite
combinatorics; the ruler convolution says the Thue–Morse sign obeys the
same recurrence; and a division-by-`n` uniqueness lemma identifies the
two.

* `eq_of_ruler_recurrence` — reusable: over any characteristic-zero
  field, the recurrence `n·c(n) = -∑_{k≤n} L(k)·c(n-k)` with `c(0)`
  fixed has a unique solution.
* `weightedPartitions n` — the finset of multiplicity vectors
  `m : ℕ →₀ ℕ` with `∑ j·mⱼ = n`.
* `partitionExpSum_recurrence` — reusable **exponential-formula
  skeleton**: for any `x` into a characteristic-zero field, the
  partition sum `P(n) = ∑_λ ∏ xⱼ^{mⱼ}/mⱼ!` obeys
  `n·P(n) = ∑_{j≤n} j·xⱼ·P(n-j)` (mark and remove one part).
* `thueMorse_partition_formula` — the atlas's partition formula
  `ε(n) = ∑_{∑j·mⱼ=n} ∏ (1/mⱼ!)(-aⱼ/j)^{mⱼ}`.
* `thueMorse_bell_formula` — the Bell-polynomial form
  `n!·ε(n) = ∑_λ n!/(∏ mⱼ!(j!)^{mⱼ})·∏(-(j-1)!·aⱼ)^{mⱼ}`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Uniqueness of the ruler recurrence** over a characteristic-zero
field: `n·c(n) = -∑_{k=1}^n L(k)·c(n-k)` together with `c(0)` pins down
the whole sequence. -/
theorem eq_of_ruler_recurrence {F : Type*} [Field F] [CharZero F]
    (L c d : ℕ → F) (h0 : c 0 = d 0)
    (hc : ∀ n : ℕ, 1 ≤ n →
      (n : F) * c n = -∑ k ∈ Icc 1 n, L k * c (n - k))
    (hd : ∀ n : ℕ, 1 ≤ n →
      (n : F) * d n = -∑ k ∈ Icc 1 n, L k * d (n - k)) :
    ∀ n, c n = d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact h0
      · have hsum : ∑ k ∈ Icc 1 n, L k * c (n - k) =
            ∑ k ∈ Icc 1 n, L k * d (n - k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have := Finset.mem_Icc.mp hk
          rw [ih (n - k) (by omega)]
        have hmul : (n : F) * c n = (n : F) * d n := by
          rw [hc n hn, hd n hn, hsum]
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) hmul

/-- The weighted partitions of `n`: finitely supported multiplicity
vectors `m` with `∑ j·mⱼ = n` (parts in `[1, n]`, multiplicities
`≤ n`). -/
noncomputable def weightedPartitions (n : ℕ) : Finset (ℕ →₀ ℕ) :=
  ((Icc 1 n).finsupp (fun _ => range (n + 1))).filter
    (fun f => ∑ j ∈ Icc 1 n, j * f j = n)

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

/-- The weighted partition sum `P(n) = ∑_λ ∏ⱼ xⱼ^{mⱼ}/mⱼ!` of a
coefficient sequence `x`. -/
noncomputable def partitionExpSum {F : Type*} [Field F]
    (x : ℕ → F) (n : ℕ) : F :=
  ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
    x j ^ f j / (f j).factorial

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

@[simp] theorem partitionExpSum_zero {F : Type*} [Field F] (x : ℕ → F) :
    partitionExpSum x 0 = 1 := by
  simp [partitionExpSum]

private theorem prod_extend {F : Type*} [Field F] (x : ℕ → F)
    (g : ℕ →₀ ℕ) {M M' : ℕ} (h : M ≤ M') (hsupp : g.support ⊆ Icc 1 M) :
    ∏ k ∈ Icc 1 M', x k ^ g k / (g k).factorial =
      ∏ k ∈ Icc 1 M, x k ^ g k / (g k).factorial := by
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

/-- **The exponential-formula recurrence**, fully general: over any
characteristic-zero field and any coefficient sequence `x`, the
partition sum obeys `n·P(n) = ∑_{j=1}^n j·xⱼ·P(n-j)`.  (Mark one part:
`n = ∑ j·mⱼ` distributes the factor `n` over the parts, and removing a
marked `j`-part is a bijection onto the partitions of `n - j`.) -/
theorem partitionExpSum_recurrence {F : Type*} [Field F] [CharZero F]
    (x : ℕ → F) (n : ℕ) :
    (n : F) * partitionExpSum x n =
      ∑ j ∈ Icc 1 n, (j : F) * x j * partitionExpSum x (n - j) := by
  -- distribute the weight over the parts
  have hstep1 : (n : F) * partitionExpSum x n =
      ∑ j ∈ Icc 1 n, ∑ f ∈ weightedPartitions n,
        ((j : F) * (f j : F)) *
          ∏ k ∈ Icc 1 n, x k ^ f k / (f k).factorial := by
    rw [partitionExpSum, Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun f hf => ?_
    have hw := (mem_weightedPartitions.mp hf).2.2
    rw [← Finset.sum_mul]
    congr 1
    have hcast : ((∑ k ∈ Icc 1 n, k * f k : ℕ) : F) =
        ∑ k ∈ Icc 1 n, (k : F) * (f k : F) := by
      push_cast
      rfl
    rw [← hcast, hw]
  rw [hstep1]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_Icc.mp hj
  -- only partitions actually containing a `j`-part contribute
  have hfilter : ∑ f ∈ weightedPartitions n,
      ((j : F) * (f j : F)) * ∏ k ∈ Icc 1 n, x k ^ f k / (f k).factorial =
      ∑ f ∈ (weightedPartitions n).filter (fun f => 1 ≤ f j),
        ((j : F) * (f j : F)) *
          ∏ k ∈ Icc 1 n, x k ^ f k / (f k).factorial := by
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
    rw [← prod_extend x (f - (Finsupp.single j 1 : ℕ →₀ ℕ))
      (M := n - j) (M' := n) (by omega) hsupp']
    rw [← Finset.mul_prod_erase (Icc 1 n)
        (fun k => x k ^ f k / (f k).factorial) hj,
      ← Finset.mul_prod_erase (Icc 1 n)
        (fun k => x k ^ (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k /
          ((f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k).factorial) hj]
    have herase : ∀ k ∈ (Icc 1 n).erase j,
        x k ^ (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k /
          ((f - (Finsupp.single j 1 : ℕ →₀ ℕ)) k).factorial =
        x k ^ f k / (f k).factorial := by
      intro k hk
      have hkj := (Finset.mem_erase.mp hk).1
      rw [happly, if_neg (fun h => hkj h.symm), Nat.sub_zero]
    rw [Finset.prod_congr rfl herase]
    have hjval : (f - (Finsupp.single j 1 : ℕ →₀ ℕ)) j = u := by
      rw [happly, if_pos rfl, hu, Nat.add_sub_cancel]
    rw [hjval, hu]
    have hfact : (((u + 1).factorial : ℕ) : F) =
        ((u : F) + 1) * ((u.factorial : ℕ) : F) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hpow : x j ^ (u + 1) = x j * x j ^ u := by
      rw [pow_succ']
    have hne1 : ((u.factorial : ℕ) : F) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hne2 : ((u : F) + 1) ≠ 0 := Nat.cast_add_one_ne_zero u
    rw [hfact, hpow]
    push_cast
    field_simp

/-- The Thue–Morse sign satisfies the ruler recurrence over `ℚ`. -/
private theorem sign_ruler_rat (n : ℕ) :
    (n : ℚ) * ((thueMorseSign n : ℤ) : ℚ) =
      -∑ k ∈ Icc 1 n, ((rulerCoeff k : ℤ) : ℚ) *
        ((thueMorseSign (n - k) : ℤ) : ℚ) := by
  have h := congrArg (fun t : ℤ => (t : ℚ)) (ruler_convolution n)
  simp only [Int.cast_mul, Int.cast_neg, Int.cast_sum,
    Int.cast_natCast] at h
  rw [h]
  congr 1

/-- The partition sum with `xⱼ = -aⱼ/j` satisfies the same ruler
recurrence. -/
private theorem partition_ruler_rat (n : ℕ) :
    (n : ℚ) * partitionExpSum
        (fun j => -((rulerCoeff j : ℤ) : ℚ) / j) n =
      -∑ k ∈ Icc 1 n, ((rulerCoeff k : ℤ) : ℚ) *
        partitionExpSum (fun j => -((rulerCoeff j : ℤ) : ℚ) / j) (n - k) := by
  rw [partitionExpSum_recurrence _ n, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hkne : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **The partition formula** (`eq:partition-formula`):
`ε(n) = ∑_{m₁+2m₂+⋯=n} ∏ⱼ (1/mⱼ!)·(-aⱼ/j)^{mⱼ}`. -/
theorem thueMorse_partition_formula (n : ℕ) :
    ((thueMorseSign n : ℤ) : ℚ) =
      ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
        (-((rulerCoeff j : ℤ) : ℚ) / j) ^ f j / (f j).factorial := by
  have h := eq_of_ruler_recurrence
    (fun k => ((rulerCoeff k : ℤ) : ℚ))
    (fun n => ((thueMorseSign n : ℤ) : ℚ))
    (partitionExpSum (fun j => -((rulerCoeff j : ℤ) : ℚ) / j))
    (by simp [thueMorseSign, binaryWeight])
    (fun n _ => sign_ruler_rat n)
    (fun n _ => partition_ruler_rat n)
    n
  rw [h]
  rfl

/-- **The Bell-polynomial form** (`eq:Bell-coefficient`):
`n!·ε(n) = ∑_λ n!/(∏ⱼ mⱼ!·(j!)^{mⱼ}) · ∏ⱼ (-(j-1)!·aⱼ)^{mⱼ}` — the
complete exponential Bell polynomial `B_n` evaluated at
`xⱼ = -(j-1)!·aⱼ`. -/
theorem thueMorse_bell_formula (n : ℕ) :
    (n.factorial : ℚ) * ((thueMorseSign n : ℤ) : ℚ) =
      ∑ f ∈ weightedPartitions n,
        (n.factorial : ℚ) /
            (∏ j ∈ Icc 1 n,
              ((f j).factorial : ℚ) * (j.factorial : ℚ) ^ f j) *
          ∏ j ∈ Icc 1 n,
            (-(((j - 1).factorial : ℚ) * ((rulerCoeff j : ℤ) : ℚ))) ^ f j := by
  rw [thueMorse_partition_formula n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hprod : ∏ j ∈ Icc 1 n,
      (-((rulerCoeff j : ℤ) : ℚ) / j) ^ f j / (f j).factorial =
      ∏ j ∈ Icc 1 n,
        ((-(((j - 1).factorial : ℚ) * ((rulerCoeff j : ℤ) : ℚ))) ^ f j /
          (((f j).factorial : ℚ) * ((j.factorial : ℚ)) ^ f j)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hjfact : (j.factorial : ℚ) =
        (j : ℚ) * (((j - 1).factorial : ℚ)) := by
      rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
    have hjne : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfne : (((j - 1).factorial : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hmne : (((f j).factorial : ℚ)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : ((j : ℚ)) ^ (f j) ≠ 0 := pow_ne_zero _ hjne
    have h2 : (((j - 1).factorial : ℚ)) ^ (f j) ≠ 0 := pow_ne_zero _ hfne
    rw [show (-(((j - 1).factorial : ℚ) * ((rulerCoeff j : ℤ) : ℚ))) =
        (-((rulerCoeff j : ℤ) : ℚ)) * (((j - 1).factorial : ℚ)) from by
      ring]
    rw [div_pow, mul_pow, hjfact, mul_pow]
    field_simp
  rw [hprod, Finset.prod_div_distrib]
  ring

end Fabius
