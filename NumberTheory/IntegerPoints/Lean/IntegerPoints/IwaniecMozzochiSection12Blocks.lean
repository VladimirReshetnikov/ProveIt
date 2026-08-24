import IntegerPoints.IwaniecMozzochi

/-!
# The finite Section 12 block cover in Iwaniec--Mozzochi

The support analysis in Section 12 produces `K < k ≤ 256 K` and
`L / 2 < l ≤ 256 L`, not one nominal dyadic block.  This module proves that
the fixed eight-by-nine family in `section12BigB` is an exact, pairwise
disjoint cover of those natural-number ranges.  It also records the uniform
scale comparisons and the elementary 72-term aggregation bound needed by
Section 13.
-/

open scoped BigOperators

namespace LeanProofs.IntegerPoints

private noncomputable def section12DyadicCover (U : ℝ) (q : ℕ) : Finset ℕ :=
  (Finset.range q).biUnion fun n ↦ dyadic ((2 : ℝ) ^ n * U)

private theorem section12DyadicCover_eq_intRange
    {U : ℝ} (hU : 0 ≤ U) (q : ℕ) :
    section12DyadicCover U q = intRange U ((2 : ℝ) ^ q * U) := by
  classical
  induction q with
  | zero =>
      simp [section12DyadicCover, intRange]
  | succ q ih =>
      have hmidNonneg : 0 ≤ (2 : ℝ) ^ q * U := by positivity
      have hU_mid : U ≤ (2 : ℝ) ^ q * U := by
        calc
          U = 1 * U := by ring
          _ ≤ (2 : ℝ) ^ q * U :=
            mul_le_mul_of_nonneg_right
              (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hU
      have hnext :
          2 * ((2 : ℝ) ^ q * U) = (2 : ℝ) ^ (q + 1) * U := by
        rw [pow_succ]
        ring
      have hmidNext :
          (2 : ℝ) ^ q * U ≤ (2 : ℝ) ^ (q + 1) * U := by
        rw [← hnext]
        linarith
      change
        (Finset.range (q + 1)).biUnion
            (fun n ↦ dyadic ((2 : ℝ) ^ n * U)) =
          intRange U ((2 : ℝ) ^ (q + 1) * U)
      rw [Finset.range_add_one, Finset.biUnion_insert]
      change
        dyadic ((2 : ℝ) ^ q * U) ∪ section12DyadicCover U q =
          intRange U ((2 : ℝ) ^ (q + 1) * U)
      rw [ih, Finset.union_comm, dyadic, hnext]
      unfold intRange
      exact Finset.Ioc_union_Ioc_eq_Ioc
        (Nat.floor_mono hU_mid) (Nat.floor_mono hmidNext)

private theorem section12_fin_biUnion_eq_cover (U : ℝ) (q : ℕ) :
    (Finset.univ : Finset (Fin q)).biUnion
        (fun j ↦ dyadic ((2 : ℝ) ^ j.val * U)) =
      section12DyadicCover U q := by
  classical
  unfold section12DyadicCover
  rw [← Finset.image_biUnion
      (f := fun j : Fin q ↦ j.val)
      (s := (Finset.univ : Finset (Fin q)))
      (t := fun n : ℕ ↦ dyadic ((2 : ℝ) ^ n * U)),
    Finset.image_fin_univ]

/-- The eight Section 12 `K` blocks form exactly `(K, 256K]` on natural
indices. -/
theorem section12KBlocks_union {K : ℝ} (hK : 0 ≤ K) :
    (Finset.univ : Finset (Fin 8)).biUnion
        (fun j ↦ dyadic (section12KBlockScale K j)) =
      intRange K (256 * K) := by
  calc
    _ = section12DyadicCover K 8 := by
      simpa [section12KBlockScale] using
        section12_fin_biUnion_eq_cover K 8
    _ = intRange K ((2 : ℝ) ^ 8 * K) :=
      section12DyadicCover_eq_intRange hK 8
    _ = intRange K (256 * K) := by norm_num

/-- The nine Section 12 `L` blocks form exactly `(L/2, 256L]` on natural
indices. -/
theorem section12LBlocks_union {L : ℝ} (hL : 0 ≤ L) :
    (Finset.univ : Finset (Fin 9)).biUnion
        (fun j ↦ dyadic (section12LBlockScale L j)) =
      intRange (L / 2) (256 * L) := by
  have hLhalf : 0 ≤ L / 2 := div_nonneg hL (by norm_num)
  calc
    _ = section12DyadicCover (L / 2) 9 := by
      simpa [section12LBlockScale] using
        section12_fin_biUnion_eq_cover (L / 2) 9
    _ = intRange (L / 2) ((2 : ℝ) ^ 9 * (L / 2)) :=
      section12DyadicCover_eq_intRange hLhalf 9
    _ = intRange (L / 2) (256 * L) := by
      congr 1
      norm_num
      ring

theorem mem_section12KRange_iff {K : ℝ} (hK : 0 ≤ K) {k : ℕ} :
    k ∈ intRange K (256 * K) ↔
      ∃ j : Fin 8, k ∈ dyadic (section12KBlockScale K j) := by
  rw [← section12KBlocks_union hK]
  simp

theorem mem_section12LNatRange_iff {L : ℝ} (hL : 0 ≤ L) {l : ℕ} :
    l ∈ intRange (L / 2) (256 * L) ↔
      ∃ j : Fin 9, l ∈ dyadic (section12LBlockScale L j) := by
  rw [← section12LBlocks_union hL]
  simp

/-- A natural Fourier index in the strict nine-block union lies in the closed
integer envelope used by equation (10.6). -/
theorem section12_natCast_mem_relevantLRange
    {L : ℝ} (hL : 0 ≤ L) {l : ℕ}
    (hl : l ∈ intRange (L / 2) (256 * L)) :
    (l : ℤ) ∈ section12RelevantLRange L := by
  have hLhalf : 0 ≤ L / 2 := div_nonneg hL (by norm_num)
  have hLupper : 0 ≤ 256 * L := mul_nonneg (by norm_num) hL
  rw [intRange, Finset.mem_Ioc] at hl
  rw [section12RelevantLRange, Finset.mem_Icc]
  have hlower : L / 2 < (l : ℝ) := (Nat.floor_lt hLhalf).mp hl.1
  have hupper : (l : ℝ) ≤ 256 * L :=
    (Nat.le_floor_iff hLupper).mp hl.2
  constructor
  · apply Int.ceil_le.mpr
    simpa only [Int.cast_natCast] using hlower.le
  · apply Int.le_floor.mpr
    simpa only [Int.cast_natCast] using hupper

private theorem section12DyadicBlocks_pairwiseDisjoint
    {U : ℝ} (hU : 0 ≤ U) (q : ℕ) :
    (((Finset.univ : Finset (Fin q)) : Set (Fin q))).PairwiseDisjoint
      (fun j ↦ dyadic ((2 : ℝ) ^ j.val * U)) := by
  classical
  have hordered :
      ∀ {i j : Fin q}, i.val < j.val →
        Disjoint (dyadic ((2 : ℝ) ^ i.val * U))
          (dyadic ((2 : ℝ) ^ j.val * U)) := by
    intro i j hij
    unfold dyadic intRange
    apply Finset.Ioc_disjoint_Ioc_of_le
    apply Nat.floor_mono
    have hp : (2 : ℝ) ^ (i.val + 1) ≤ (2 : ℝ) ^ j.val :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
        (Nat.succ_le_of_lt hij)
    have hm := mul_le_mul_of_nonneg_right hp hU
    simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hm
  intro i _ j _ hij
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hijv | hjiv
  · exact hordered hijv
  · exact (hordered hjiv).symm

theorem section12KBlocks_pairwiseDisjoint {K : ℝ} (hK : 0 ≤ K) :
    (((Finset.univ : Finset (Fin 8)) : Set (Fin 8))).PairwiseDisjoint
      (fun j ↦ dyadic (section12KBlockScale K j)) := by
  simpa [section12KBlockScale] using
    section12DyadicBlocks_pairwiseDisjoint hK 8

theorem section12LBlocks_pairwiseDisjoint {L : ℝ} (hL : 0 ≤ L) :
    (((Finset.univ : Finset (Fin 9)) : Set (Fin 9))).PairwiseDisjoint
      (fun j ↦ dyadic (section12LBlockScale L j)) := by
  have hLhalf : 0 ≤ L / 2 := div_nonneg hL (by norm_num)
  simpa [section12LBlockScale] using
    section12DyadicBlocks_pairwiseDisjoint hLhalf 9

theorem section12KRange_card_eq_sum_cards {K : ℝ} (hK : 0 ≤ K) :
    (intRange K (256 * K)).card =
      ∑ j : Fin 8, (dyadic (section12KBlockScale K j)).card := by
  rw [← section12KBlocks_union hK]
  simpa using Finset.card_biUnion (section12KBlocks_pairwiseDisjoint hK)

theorem section12LNatRange_card_eq_sum_cards {L : ℝ} (hL : 0 ≤ L) :
    (intRange (L / 2) (256 * L)).card =
      ∑ j : Fin 9, (dyadic (section12LBlockScale L j)).card := by
  rw [← section12LBlocks_union hL]
  simpa using Finset.card_biUnion (section12LBlocks_pairwiseDisjoint hL)

theorem section12KBlockScale_nonneg {K : ℝ} (hK : 0 ≤ K) (j : Fin 8) :
    0 ≤ section12KBlockScale K j := by
  unfold section12KBlockScale
  positivity

theorem section12LBlockScale_nonneg {L : ℝ} (hL : 0 ≤ L) (j : Fin 9) :
    0 ≤ section12LBlockScale L j := by
  unfold section12LBlockScale
  positivity

theorem section12KBlockScale_lower {K : ℝ} (hK : 0 ≤ K) (j : Fin 8) :
    K ≤ section12KBlockScale K j := by
  unfold section12KBlockScale
  calc
    K = 1 * K := by ring
    _ ≤ (2 : ℝ) ^ j.val * K :=
      mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hK

theorem section12KBlockScale_upper {K : ℝ} (hK : 0 ≤ K) (j : Fin 8) :
    section12KBlockScale K j ≤ 128 * K := by
  have hj : j.val ≤ 7 := by omega
  unfold section12KBlockScale
  calc
    (2 : ℝ) ^ j.val * K ≤ (2 : ℝ) ^ 7 * K :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj) hK
    _ = 128 * K := by norm_num

theorem section12LBlockScale_lower {L : ℝ} (hL : 0 ≤ L) (j : Fin 9) :
    L / 2 ≤ section12LBlockScale L j := by
  unfold section12LBlockScale
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
      (div_nonneg hL (by norm_num))

theorem section12LBlockScale_upper {L : ℝ} (hL : 0 ≤ L) (j : Fin 9) :
    section12LBlockScale L j ≤ 128 * L := by
  have hj : j.val ≤ 8 := by omega
  unfold section12LBlockScale
  calc
    (2 : ℝ) ^ j.val * (L / 2) ≤ (2 : ℝ) ^ 8 * (L / 2) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hj)
        (div_nonneg hL (by norm_num))
    _ = 128 * L := by ring

theorem bigB_nonneg
    {x G A C K L t₁ t₂ : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) :
    0 ≤ bigB x G A C K L t₁ t₂ := by
  unfold bigB
  apply mul_nonneg (div_nonneg hG hC)
  exact Finset.sum_nonneg fun _a _ha ↦
    Finset.sum_nonneg fun _c _hc ↦ norm_nonneg _

theorem section12BigB_nonneg
    {x G A C K L t₁ t₂ : ℝ} (hG : 0 ≤ G) (hC : 0 ≤ C) :
    0 ≤ section12BigB x G A C K L t₁ t₂ := by
  unfold section12BigB
  exact Finset.sum_nonneg fun _jK _hjK ↦
    Finset.sum_nonneg fun _jL _hjL ↦ bigB_nonneg hG hC

/-- A uniform bound for all 72 single blocks sums to the corresponding bound
for the full Section 12 aggregate. -/
theorem section12BigB_le_72_mul
    {x G A C K L t₁ t₂ B : ℝ}
    (hblock : ∀ jK : Fin 8, ∀ jL : Fin 9,
      bigB x G A C (section12KBlockScale K jK)
          (section12LBlockScale L jL) t₁ t₂ ≤ B) :
    section12BigB x G A C K L t₁ t₂ ≤ 72 * B := by
  unfold section12BigB
  calc
    _ ≤ ∑ _jK : Fin 8, ∑ _jL : Fin 9, B := by
      exact Finset.sum_le_sum fun jK _ ↦
        Finset.sum_le_sum fun jL _ ↦ hblock jK jL
    _ = 72 * B := by
      simp
      ring

end LeanProofs.IntegerPoints
