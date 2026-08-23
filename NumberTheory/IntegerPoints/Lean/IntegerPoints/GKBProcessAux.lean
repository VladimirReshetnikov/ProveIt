import IntegerPoints.KuzminLandau

/-!
# Graham--Kolesnik, Theorem 3.10: B-process auxiliaries

This module collects the finite-sum and interval bookkeeping needed by the
Graham--Kolesnik B-process.  It deliberately contains no exponent arithmetic:
the results below are reusable independently of the particular exponent-pair
estimate eventually applied to the dual phase.

There are three small interface boundaries to cross.

* Lemma 3.6 returns a sum indexed by the integer interval
  `Finset.Icc ⌈A⌉ ⌊B⌋`, whereas `IsExponentPair` is stated for the
  natural interval `intRange A B = (⌊A⌋, ⌊B⌋]`.  For nonnegative
  frequencies the closed integer interval is exactly `closedRange A B`; the
  latter differs from `intRange A B` in at most its lower endpoint.
* The phase furnished by Lemma 3.6 is the negative Legendre phase, with the
  harmless constant `-1/8`.  Fixed real phase shifts and conjugation do not
  alter the norm of an exponential sum.
* The stationary-phase amplitude is a nonnegative monotone weight.  The Abel
  inequality below bounds a weighted complex sum by the largest prefix-sum
  norm times its first weight.

The dyadic-cut lemmas express the interval occurring in
`gk_lemma39_class_holds` literally as the intersection of a derivative range
with a dyadic block.  This keeps the later B-process proof at the level of the
existing APIs rather than repeatedly unfolding floors.
-/

open scoped BigOperators
open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## Fixed phase shifts and phase reversal -/

/-- Pull a fixed additive phase out of a finite exponential sum. -/
theorem sum_e_add_const {ι : Type*} (S : Finset ι) (phase : ι → ℝ) (c : ℝ) :
    ∑ i ∈ S, e (c + phase i) = e c * ∑ i ∈ S, e (phase i) := by
  calc
    ∑ i ∈ S, e (c + phase i) = ∑ i ∈ S, e c * e (phase i) := by
      exact Finset.sum_congr rfl fun i _ => KL.e_add c (phase i)
    _ = e c * ∑ i ∈ S, e (phase i) := by rw [Finset.mul_sum]

/-- A fixed additive phase does not change the norm of an exponential sum. -/
theorem norm_sum_e_add_const {ι : Type*} (S : Finset ι) (phase : ι → ℝ) (c : ℝ) :
    ‖∑ i ∈ S, e (c + phase i)‖ = ‖∑ i ∈ S, e (phase i)‖ := by
  rw [sum_e_add_const, norm_mul, norm_e, one_mul]

/-- Reversing every real phase conjugates the corresponding finite sum. -/
theorem sum_e_neg {ι : Type*} (S : Finset ι) (phase : ι → ℝ) :
    ∑ i ∈ S, e (-phase i) = starRingEnd ℂ (∑ i ∈ S, e (phase i)) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => KL.e_neg (phase i)

/-- Reversing every real phase does not change the norm of the sum. -/
theorem norm_sum_e_neg {ι : Type*} (S : Finset ι) (phase : ι → ℝ) :
    ‖∑ i ∈ S, e (-phase i)‖ = ‖∑ i ∈ S, e (phase i)‖ := by
  rw [sum_e_neg, starRingEnd_apply, norm_star]

/-- The combination used in the B-process: a fixed phase minus the dual phase. -/
theorem norm_sum_e_const_sub {ι : Type*} (S : Finset ι) (phase : ι → ℝ) (c : ℝ) :
    ‖∑ i ∈ S, e (c - phase i)‖ = ‖∑ i ∈ S, e (phase i)‖ := by
  calc
    ‖∑ i ∈ S, e (c - phase i)‖ = ‖∑ i ∈ S, e (-phase i)‖ := by
      simpa [sub_eq_add_neg] using norm_sum_e_add_const S (fun i => -phase i) c
    _ = ‖∑ i ∈ S, e (phase i)‖ := norm_sum_e_neg S phase

/-! ## Closed integer frequencies versus `intRange` -/

/--
For a nonnegative real interval, casting natural numbers gives a bijection
between `closedRange A B` and the closed integer-frequency interval used by
Lemma 3.6.
-/
theorem sum_integer_Icc_eq_sum_closedRange {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B)
    (g : ℤ → ℂ) :
    ∑ ν ∈ Finset.Icc ⌈A⌉ ⌊B⌋, g ν = ∑ n ∈ closedRange A B, g n := by
  classical
  have hB : 0 ≤ B := hA.trans hAB
  refine Finset.sum_bij' (fun ν _ => ν.toNat) (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro ν hν
    rw [Finset.mem_Icc] at hν
    rw [closedRange, Finset.mem_Icc]
    have hν0 : 0 ≤ ν := (Int.ceil_nonneg hA).trans hν.1
    constructor
    · have hl : (⌈A⌉₊ : ℤ) ≤ (ν.toNat : ℤ) := by
        rw [Int.natCast_ceil_eq_ceil hA, Int.toNat_of_nonneg hν0]
        exact hν.1
      exact_mod_cast hl
    · have hu : (ν.toNat : ℤ) ≤ (⌊B⌋₊ : ℤ) := by
        rw [Int.toNat_of_nonneg hν0, Int.natCast_floor_eq_floor hB]
        exact hν.2
      exact_mod_cast hu
  · intro n hn
    rw [closedRange, Finset.mem_Icc] at hn
    rw [Finset.mem_Icc]
    constructor
    · rw [← Int.natCast_ceil_eq_ceil hA]
      exact_mod_cast hn.1
    · rw [← Int.natCast_floor_eq_floor hB]
      exact_mod_cast hn.2
  · intro ν hν
    rw [Finset.mem_Icc] at hν
    exact Int.toNat_of_nonneg ((Int.ceil_nonneg hA).trans hν.1)
  · intro n _
    simp
  · intro ν hν
    rw [Finset.mem_Icc] at hν
    congr 1
    exact (Int.toNat_of_nonneg ((Int.ceil_nonneg hA).trans hν.1)).symm

/-- The half-open range in `IsExponentPair` is contained in the closed range. -/
theorem intRange_subset_closedRange (A B : ℝ) : intRange A B ⊆ closedRange A B := by
  intro n hn
  rw [intRange, Finset.mem_Ioc] at hn
  rw [closedRange, Finset.mem_Icc]
  have hceil := Nat.ceil_le_floor_add_one A
  omega

/-- The closed and half-open natural ranges can differ only at the lower endpoint. -/
theorem closedRange_sdiff_intRange_subset_singleton (A B : ℝ) :
    closedRange A B \ intRange A B ⊆ {⌈A⌉₊} := by
  intro n hn
  rw [Finset.mem_sdiff, closedRange, intRange, Finset.mem_Icc, Finset.mem_Ioc] at hn
  rw [Finset.mem_singleton]
  have hfloor_ceil := Nat.floor_le_ceil A
  omega

/-- Consequently, deleting the lower endpoint removes at most one term. -/
theorem card_closedRange_sdiff_intRange_le_one (A B : ℝ) :
    (closedRange A B \ intRange A B).card ≤ 1 := by
  calc
    (closedRange A B \ intRange A B).card ≤ ({⌈A⌉₊} : Finset ℕ).card :=
      Finset.card_le_card (closedRange_sdiff_intRange_subset_singleton A B)
    _ = 1 := Finset.card_singleton _

/--
Replacing a closed natural interval by `intRange` costs at most the uniform
norm bound for one summand.
-/
theorem norm_sum_closedRange_le_norm_sum_intRange_add (A B R : ℝ) (g : ℕ → ℂ)
    (hR : 0 ≤ R) (hg : ∀ n ∈ closedRange A B, ‖g n‖ ≤ R) :
    ‖∑ n ∈ closedRange A B, g n‖ ≤ ‖∑ n ∈ intRange A B, g n‖ + R := by
  have hsub := intRange_subset_closedRange A B
  have herror : ‖∑ n ∈ closedRange A B \ intRange A B, g n‖ ≤ R := by
    calc
      ‖∑ n ∈ closedRange A B \ intRange A B, g n‖ ≤
          ∑ n ∈ closedRange A B \ intRange A B, ‖g n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ closedRange A B \ intRange A B, R := by
        refine Finset.sum_le_sum ?_
        intro n hn
        exact hg n (Finset.mem_sdiff.mp hn).1
      _ = ((closedRange A B \ intRange A B).card : ℝ) * R := by simp
      _ ≤ 1 * R := mul_le_mul_of_nonneg_right (by
        exact_mod_cast card_closedRange_sdiff_intRange_le_one A B) hR
      _ = R := one_mul R
  rw [← Finset.sum_sdiff hsub]
  calc
    ‖(∑ n ∈ closedRange A B \ intRange A B, g n) + ∑ n ∈ intRange A B, g n‖ ≤
        ‖∑ n ∈ closedRange A B \ intRange A B, g n‖ +
          ‖∑ n ∈ intRange A B, g n‖ := norm_add_le _ _
    _ ≤ R + ‖∑ n ∈ intRange A B, g n‖ := add_le_add herror le_rfl
    _ = ‖∑ n ∈ intRange A B, g n‖ + R := add_comm _ _

/-- The unit-summand specialization used for ordinary exponential sums. -/
theorem norm_sum_closedRange_le_norm_sum_intRange_add_one (A B : ℝ) (g : ℕ → ℂ)
    (hg : ∀ n ∈ closedRange A B, ‖g n‖ ≤ 1) :
    ‖∑ n ∈ closedRange A B, g n‖ ≤ ‖∑ n ∈ intRange A B, g n‖ + 1 := by
  simpa using norm_sum_closedRange_le_norm_sum_intRange_add A B 1 g zero_le_one hg

/--
The exact bridge needed after Lemma 3.6: a closed integer exponential sum is
bounded by the corresponding `IsExponentPair` sum, with one endpoint term.
-/
theorem norm_sum_integer_Icc_e_le_norm_intRange_e_add_one {A B : ℝ}
    (hA : 0 ≤ A) (hAB : A ≤ B) (phase : ℝ → ℝ) :
    ‖∑ ν ∈ Finset.Icc ⌈A⌉ ⌊B⌋, e (phase (ν : ℝ))‖ ≤
      ‖∑ n ∈ intRange A B, e (phase (n : ℝ))‖ + 1 := by
  rw [sum_integer_Icc_eq_sum_closedRange hA hAB
    (fun ν : ℤ => e (phase (ν : ℝ)))]
  exact norm_sum_closedRange_le_norm_sum_intRange_add_one A B
    (fun n : ℕ => e (phase (n : ℝ))) (by simp [norm_e])

/-! ## Dyadic cuts and intersections -/

/-- The `j`-th cut in the dyadic decomposition beginning at `J`. -/
noncomputable def dyadicCut (J : ℝ) (j : ℕ) : ℝ := (2 : ℝ) ^ j * J

@[simp]
theorem dyadicCut_zero (J : ℝ) : dyadicCut J 0 = J := by simp [dyadicCut]

/-- Consecutive cuts differ by a factor of two. -/
theorem dyadicCut_succ (J : ℝ) (j : ℕ) : dyadicCut J (j + 1) = 2 * dyadicCut J j := by
  simp only [dyadicCut, pow_succ]
  ring

theorem dyadicCut_pos {J : ℝ} (hJ : 0 < J) (j : ℕ) : 0 < dyadicCut J j := by
  unfold dyadicCut
  positivity

theorem dyadicCut_nonneg {J : ℝ} (hJ : 0 ≤ J) (j : ℕ) : 0 ≤ dyadicCut J j := by
  unfold dyadicCut
  positivity

/-- Dyadic cuts are increasing when the initial cut is nonnegative. -/
theorem dyadicCut_le_succ {J : ℝ} (hJ : 0 ≤ J) (j : ℕ) :
    dyadicCut J j ≤ dyadicCut J (j + 1) := by
  rw [dyadicCut_succ]
  linarith [dyadicCut_nonneg hJ j]

theorem dyadicCut_monotone {J : ℝ} (hJ : 0 ≤ J) : Monotone (dyadicCut J) :=
  monotone_nat_of_le_succ (dyadicCut_le_succ hJ)

/-- Every real upper endpoint is eventually passed by positive dyadic cuts. -/
theorem exists_lt_dyadicCut {J B : ℝ} (hJ : 0 < J) : ∃ q : ℕ, B < dyadicCut J q := by
  obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt (B / J) (by norm_num : (1 : ℝ) < 2)
  refine ⟨q, ?_⟩
  calc
    B = (B / J) * J := (div_mul_cancel₀ B hJ.ne').symm
    _ < (2 : ℝ) ^ q * J := mul_lt_mul_of_pos_right hq hJ
    _ = dyadicCut J q := rfl

/-- Intersecting two real half-open ranges intersects their endpoints. -/
theorem intRange_inter_intRange (A B C D : ℝ) :
    intRange A B ∩ intRange C D = intRange (max A C) (min B D) := by
  unfold intRange
  rw [Finset.Ioc_inter_Ioc, Nat.floor_mono.map_max, Nat.floor_mono.map_min]

/-- The interval passed to Lemma 3.9 is exactly a range--dyadic intersection. -/
theorem intRange_inter_dyadic (A B J : ℝ) :
    intRange A B ∩ dyadic J = intRange (max A J) (min B (2 * J)) := by
  rw [dyadic, intRange_inter_intRange]

/-- The same intersection with its upper endpoint expressed as the next cut. -/
theorem intRange_inter_dyadicCut (A B J : ℝ) (j : ℕ) :
    intRange A B ∩ dyadic (dyadicCut J j) =
      intRange (max A (dyadicCut J j)) (min B (dyadicCut J (j + 1))) := by
  rw [intRange_inter_dyadic, dyadicCut_succ]

/-- Adjacent dyadic cut intervals are disjoint despite sharing a real endpoint. -/
theorem disjoint_intRange_dyadicCuts (J : ℝ) (j : ℕ) :
    Disjoint (intRange (dyadicCut J j) (dyadicCut J (j + 1)))
      (intRange (dyadicCut J (j + 1)) (dyadicCut J (j + 2))) := by
  unfold intRange
  exact Finset.Ioc_disjoint_Ioc_of_le le_rfl

/-- Two adjacent dyadic cut intervals merge into the interval spanning both. -/
theorem intRange_dyadicCuts_union_succ {J : ℝ} (hJ : 0 ≤ J) (j : ℕ) :
    intRange (dyadicCut J j) (dyadicCut J (j + 1)) ∪
        intRange (dyadicCut J (j + 1)) (dyadicCut J (j + 2)) =
      intRange (dyadicCut J j) (dyadicCut J (j + 2)) := by
  unfold intRange
  exact Finset.Ioc_union_Ioc_eq_Ioc
    (Nat.floor_mono (dyadicCut_le_succ hJ j))
    (Nat.floor_mono (dyadicCut_le_succ hJ (j + 1)))

/-! ## Complex Abel summation with antitone real weights -/

/-- The inclusive prefix sum `a 0 + ... + a K`. -/
noncomputable def prefixSum (a : ℕ → ℂ) (K : ℕ) : ℂ :=
  ∑ i ∈ Finset.range (K + 1), a i

@[simp]
theorem prefixSum_zero (a : ℕ → ℂ) : prefixSum a 0 = a 0 := by simp [prefixSum]

/-- Extend an inclusive prefix sum by its next term. -/
theorem prefixSum_succ (a : ℕ → ℂ) (K : ℕ) :
    prefixSum a (K + 1) = prefixSum a K + a (K + 1) := by
  simp [prefixSum, Finset.sum_range_succ]

/-- Abel's finite summation identity in prefix-sum form. -/
theorem weighted_sum_eq_last_prefix_add_sum_drops (a : ℕ → ℂ) (w : ℕ → ℝ) (K : ℕ) :
    ∑ i ∈ Finset.range (K + 1), (w i : ℂ) * a i =
      (w K : ℂ) * prefixSum a K +
        ∑ i ∈ Finset.range K,
          ((w i - w (i + 1) : ℝ) : ℂ) * prefixSum a i := by
  induction K with
  | zero => simp [prefixSum]
  | succ K ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, prefixSum_succ]
      push_cast
      ring

/-- The last weight plus all successive drops telescopes to the first weight. -/
theorem last_weight_add_sum_drops (w : ℕ → ℝ) (K : ℕ) :
    w K + ∑ i ∈ Finset.range K, (w i - w (i + 1)) = w 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ]
      linarith

/--
Complex Abel inequality.  If `w` is nonnegative and antitone through index
`K`, and every inclusive prefix of `a` has norm at most `M`, then the weighted
sum has norm at most `M * w 0`.
-/
theorem norm_weighted_sum_le (a : ℕ → ℂ) (w : ℕ → ℝ) (K : ℕ) (M : ℝ)
    (hw_nonneg : ∀ i, i ≤ K → 0 ≤ w i)
    (hw_antitone : ∀ i, i < K → w (i + 1) ≤ w i)
    (hprefix : ∀ i, i ≤ K → ‖prefixSum a i‖ ≤ M) :
    ‖∑ i ∈ Finset.range (K + 1), (w i : ℂ) * a i‖ ≤ M * w 0 := by
  have hwK : 0 ≤ w K := hw_nonneg K le_rfl
  have hdrop : ∀ i ∈ Finset.range K, 0 ≤ w i - w (i + 1) := by
    intro i hi
    exact sub_nonneg.mpr (hw_antitone i (Finset.mem_range.mp hi))
  have hlast : ‖(w K : ℂ) * prefixSum a K‖ ≤ w K * M := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hwK]
    exact mul_le_mul_of_nonneg_left (hprefix K le_rfl) hwK
  have hterms :
      ∑ i ∈ Finset.range K,
          ‖((w i - w (i + 1) : ℝ) : ℂ) * prefixSum a i‖ ≤
        ∑ i ∈ Finset.range K, (w i - w (i + 1)) * M := by
    refine Finset.sum_le_sum ?_
    intro i hi
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hdrop i hi)]
    exact mul_le_mul_of_nonneg_left
      (hprefix i (Nat.le_of_lt (Finset.mem_range.mp hi))) (hdrop i hi)
  rw [weighted_sum_eq_last_prefix_add_sum_drops]
  calc
    ‖(w K : ℂ) * prefixSum a K +
        ∑ i ∈ Finset.range K,
          ((w i - w (i + 1) : ℝ) : ℂ) * prefixSum a i‖ ≤
        ‖(w K : ℂ) * prefixSum a K‖ +
          ‖∑ i ∈ Finset.range K,
            ((w i - w (i + 1) : ℝ) : ℂ) * prefixSum a i‖ := norm_add_le _ _
    _ ≤ ‖(w K : ℂ) * prefixSum a K‖ +
        ∑ i ∈ Finset.range K,
          ‖((w i - w (i + 1) : ℝ) : ℂ) * prefixSum a i‖ :=
      add_le_add le_rfl (norm_sum_le _ _)
    _ ≤ w K * M + ∑ i ∈ Finset.range K, (w i - w (i + 1)) * M :=
      add_le_add hlast hterms
    _ = M * (w K + ∑ i ∈ Finset.range K, (w i - w (i + 1))) := by
      rw [← Finset.sum_mul]
      ring
    _ = M * w 0 := by rw [last_weight_add_sum_drops]

/-- A convenient specialization taking a globally antitone weight. -/
theorem norm_weighted_sum_le_of_antitone (a : ℕ → ℂ) (w : ℕ → ℝ) (K : ℕ) (M : ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i) (hw_antitone : Antitone w)
    (hprefix : ∀ i, i ≤ K → ‖prefixSum a i‖ ≤ M) :
    ‖∑ i ∈ Finset.range (K + 1), (w i : ℂ) * a i‖ ≤ M * w 0 :=
  norm_weighted_sum_le a w K M (fun i _ => hw_nonneg i)
    (fun i _ => hw_antitone (Nat.le_succ i)) hprefix

/--
Shifted-interval form of the Abel inequality.  This is the form used on each
dyadic frequency block: every prefix beginning immediately after `A` is
controlled, and the weight is antitone on `[A+1,B]`.
-/
theorem norm_sum_Ioc_weight_mul_le {A B : ℕ} (hAB : A < B) (a : ℕ → ℂ) (w : ℕ → ℝ)
    (M : ℝ) (hw_nonneg : ∀ n ∈ Finset.Ioc A B, 0 ≤ w n)
    (hw_antitone : AntitoneOn w (Set.Icc (A + 1) B))
    (hprefix : ∀ T ∈ Finset.Ioc A B, ‖∑ n ∈ Finset.Ioc A T, a n‖ ≤ M) :
    ‖∑ n ∈ Finset.Ioc A B, (w n : ℂ) * a n‖ ≤ M * w (A + 1) := by
  let K := B - A - 1
  have hlength : B - A = K + 1 := by
    dsimp [K]
    omega
  have hw_nonneg' : ∀ i, i ≤ K → 0 ≤ w (A + 1 + i) := by
    intro i hi
    apply hw_nonneg
    rw [Finset.mem_Ioc]
    dsimp [K] at hi
    omega
  have hw_antitone' : ∀ i, i < K → w (A + 1 + (i + 1)) ≤ w (A + 1 + i) := by
    intro i hi
    dsimp [K] at hi
    apply hw_antitone
    · constructor <;> omega
    · constructor <;> omega
    · omega
  have hprefix' : ∀ i, i ≤ K →
      ‖prefixSum (fun j => a (A + 1 + j)) i‖ ≤ M := by
    intro i hi
    have hT : A + 1 + i ∈ Finset.Ioc A B := by
      rw [Finset.mem_Ioc]
      dsimp [K] at hi
      omega
    have heq : prefixSum (fun j => a (A + 1 + j)) i =
        ∑ n ∈ Finset.Ioc A (A + 1 + i), a n := by
      rw [KL.sum_Ioc_eq_sum_range]
      simp only [prefixSum]
      rw [show A + 1 + i - A = i + 1 by omega]
    rw [heq]
    exact hprefix (A + 1 + i) hT
  rw [KL.sum_Ioc_eq_sum_range, hlength]
  simpa using norm_weighted_sum_le
    (fun i => a (A + 1 + i)) (fun i => w (A + 1 + i)) K M
      hw_nonneg' hw_antitone' hprefix'

end GKB

end LeanProofs.IntegerPoints
