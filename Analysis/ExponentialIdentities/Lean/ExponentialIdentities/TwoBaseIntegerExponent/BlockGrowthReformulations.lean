import ExponentialIdentities.TwoBaseIntegerExponent.QuadraticAsymptotic

/-!
# Block-growth reformulations of the Alaoglu--Erdős conjecture

Let
`B T = #(twoBaseNaturalCandidatesInDyadicBlock T)`
be the number of two-base natural candidates in the dyadic block `[2 ^ T, 2 ^ (T + 1))`.
This file proves the *block-growth reformulations*: the conjecture is equivalent to each of

* `B` is bounded;
* `B T = o(T)`;
* `liminf B T / T = 0`;
* `B T = 1` for every `T`.

The proof is a clean dichotomy supplied by the exact conditional counting already in the
repository.

*Success side.*  If the conjecture holds, `twoBaseNaturalCandidatesInDyadicBlock T` is the
singleton `{2 ^ T}` (`QuadraticAsymptotic`), hence `B T = 1` and all four properties hold.

*Failure side.*  If the conjecture fails, `ExactCounting` supplies the canonical least
generator `β > 0` together with the exact block formula
`B T = 1 + ⌊(T + 1) / β⌋₊`.  Since `⌊x⌋₊ + 1 ≥ x`, this gives the unconditional linear lower
bound `T / β ≤ B T`, which simultaneously destroys boundedness, the `o(T)` bound, and the
vanishing lower density.  (The report's sharper statement is `B T / T → 1 / β`; the one-sided
bound is all four equivalences need, and it avoids a squeeze argument.)

Note on formulation (iii).  Working with `Filter.liminf` over `ℝ` would drag in
`IsBoundedUnder`/`IsCoboundedUnder` side conditions in the direction that matters here, so the
`liminf = 0` clause is stated in its unfolded, side-condition-free form:
`∀ ε > 0, ∃ᶠ T in atTop, B T < ε * T`.  For a nonnegative sequence this is exactly
`liminf (B T / T) = 0`.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Set Filter Asymptotics

noncomputable section

/-- The dyadic block count `B T`: the number of two-base natural candidates in
`[2 ^ T, 2 ^ (T + 1))`. -/
def dyadicBlockCount (T : ℕ) : ℕ :=
  (twoBaseNaturalCandidatesInDyadicBlock T).card

/-- Under the conjecture every dyadic block contains exactly one candidate, namely its
left endpoint `2 ^ T`. -/
theorem dyadicBlockCount_eq_one_of_alaogluErdosConjecture
    (hconj : AlaogluErdosConjecture) (T : ℕ) :
    dyadicBlockCount T = 1 := by
  rw [dyadicBlockCount,
    twoBaseNaturalCandidatesInDyadicBlock_eq_singleton_of_alaogluErdosConjecture hconj,
    Finset.card_singleton]

/-- If the conjecture fails, the exact block formula `B T = 1 + ⌊(T + 1) / β⌋₊` forces a
strictly positive linear lower bound `c * T ≤ B T`, with `c = 1 / β`. -/
theorem exists_pos_linear_lower_bound_dyadicBlockCount_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, c * (T : ℝ) ≤ (dyadicBlockCount T : ℝ) := by
  obtain ⟨β, _, hβleast, _, _, _, hblock, _⟩ :=
    exists_primitiveGenerator_with_exact_counting hfail
  have hβpos : 0 < β := hβleast.pos
  refine ⟨1 / β, div_pos one_pos hβpos, ?_⟩
  intro T
  have hfloor : ((T : ℝ) + 1) / β ≤ (⌊((T : ℝ) + 1) / β⌋₊ : ℝ) + 1 :=
    (Nat.lt_floor_add_one _).le
  have hsplit : ((T : ℝ) + 1) / β = (T : ℝ) / β + 1 / β := add_div _ _ _
  have hinv : (0 : ℝ) < 1 / β := div_pos one_pos hβpos
  calc
    1 / β * (T : ℝ) = (T : ℝ) / β := by ring
    _ ≤ 1 + (⌊((T : ℝ) + 1) / β⌋₊ : ℝ) := by linarith [hsplit, hfloor, hinv]
    _ = (dyadicBlockCount T : ℝ) := by
        rw [dyadicBlockCount, hblock T, Nat.cast_add, Nat.cast_one]

/-- If the conjecture fails, the dyadic block counts are unbounded: they eventually exceed
every real threshold. -/
theorem exists_dyadicBlockCount_gt_of_not_alaogluErdosConjecture
    (hfail : ¬ AlaogluErdosConjecture) (C : ℝ) :
    ∃ T : ℕ, C < (dyadicBlockCount T : ℝ) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_pos_linear_lower_bound_dyadicBlockCount_of_not_alaogluErdosConjecture hfail
  have hcne : c ≠ 0 := ne_of_gt hc
  obtain ⟨T, hT⟩ := exists_nat_gt (C / c)
  have hcancel : c * (C / c) = C := by field_simp
  have hlt : C < c * (T : ℝ) := by
    have h := mul_lt_mul_of_pos_left hT hc
    rwa [hcancel] at h
  exact ⟨T, lt_of_lt_of_le hlt (hbound T)⟩

/-- **Block-growth reformulation (iv).**  The conjecture is equivalent to every dyadic block
containing exactly one candidate. -/
theorem alaogluErdosConjecture_iff_dyadicBlock_eq_one :
    AlaogluErdosConjecture ↔ ∀ T : ℕ, dyadicBlockCount T = 1 := by
  constructor
  · exact dyadicBlockCount_eq_one_of_alaogluErdosConjecture
  · intro hone
    by_contra hfail
    obtain ⟨T, hT⟩ := exists_dyadicBlockCount_gt_of_not_alaogluErdosConjecture hfail 1
    rw [hone T] at hT
    norm_num at hT

/-- **Block-growth reformulation (i).**  The conjecture is equivalent to boundedness of the
dyadic block counts. -/
theorem alaogluErdosConjecture_iff_dyadicBlock_bounded :
    AlaogluErdosConjecture ↔ ∃ C : ℕ, ∀ T : ℕ, dyadicBlockCount T ≤ C := by
  constructor
  · intro hconj
    exact ⟨1, fun T ↦
      le_of_eq (dyadicBlockCount_eq_one_of_alaogluErdosConjecture hconj T)⟩
  · rintro ⟨C, hC⟩
    by_contra hfail
    obtain ⟨T, hT⟩ :=
      exists_dyadicBlockCount_gt_of_not_alaogluErdosConjecture hfail (C : ℝ)
    have hle : (dyadicBlockCount T : ℝ) ≤ (C : ℝ) := by exact_mod_cast hC T
    linarith

/-- **Block-growth reformulation (ii).**  The conjecture is equivalent to `B T = o(T)`. -/
theorem alaogluErdosConjecture_iff_dyadicBlock_isLittleO :
    AlaogluErdosConjecture ↔
      (fun T : ℕ ↦ (dyadicBlockCount T : ℝ)) =o[atTop] fun T : ℕ ↦ (T : ℝ) := by
  constructor
  · intro hconj
    rw [isLittleO_iff]
    intro c hc
    have hcne : c ≠ 0 := ne_of_gt hc
    obtain ⟨T₀, hT₀⟩ := exists_nat_gt (1 / c)
    have hcancel : c * (1 / c) = 1 := by field_simp
    have h1 : (1 : ℝ) < c * (T₀ : ℝ) := by
      have h := mul_lt_mul_of_pos_left hT₀ hc
      rwa [hcancel] at h
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hTle : (T₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have h2 : c * (T₀ : ℝ) ≤ c * (T : ℝ) := mul_le_mul_of_nonneg_left hTle hc.le
    have hone := dyadicBlockCount_eq_one_of_alaogluErdosConjecture hconj T
    simp only [hone, Nat.cast_one, norm_one, Real.norm_natCast]
    linarith
  · intro hlittle
    by_contra hfail
    obtain ⟨c, hc, hbound⟩ :=
      exists_pos_linear_lower_bound_dyadicBlockCount_of_not_alaogluErdosConjecture hfail
    have hhalf : (0 : ℝ) < c / 2 := by linarith
    have hev := isLittleO_iff.mp hlittle hhalf
    obtain ⟨T, hTle, hT1⟩ := (hev.and (eventually_ge_atTop 1)).exists
    simp only [Real.norm_natCast] at hTle
    have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
    have hpos : 0 < c * (T : ℝ) := mul_pos hc (by linarith)
    have hlow := hbound T
    linarith

/-- **Block-growth reformulation (iii).**  The conjecture is equivalent to the vanishing of
the lower density `liminf B T / T`, stated in the side-condition-free form
`∀ ε > 0, ∃ᶠ T in atTop, B T < ε * T`. -/
theorem alaogluErdosConjecture_iff_dyadicBlock_liminf_zero :
    AlaogluErdosConjecture ↔
      ∀ ε : ℝ, 0 < ε → ∃ᶠ T : ℕ in atTop, (dyadicBlockCount T : ℝ) < ε * (T : ℝ) := by
  constructor
  · intro hconj ε hε
    have hεne : ε ≠ 0 := ne_of_gt hε
    obtain ⟨T₀, hT₀⟩ := exists_nat_gt (1 / ε)
    have hcancel : ε * (1 / ε) = 1 := by field_simp
    have h1 : (1 : ℝ) < ε * (T₀ : ℝ) := by
      have h := mul_lt_mul_of_pos_left hT₀ hε
      rwa [hcancel] at h
    refine Filter.Eventually.frequently ?_
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have hTle : (T₀ : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have h2 : ε * (T₀ : ℝ) ≤ ε * (T : ℝ) := mul_le_mul_of_nonneg_left hTle hε.le
    have hone := dyadicBlockCount_eq_one_of_alaogluErdosConjecture hconj T
    simp only [hone, Nat.cast_one]
    linarith
  · intro hfreq
    by_contra hfail
    obtain ⟨c, hc, hbound⟩ :=
      exists_pos_linear_lower_bound_dyadicBlockCount_of_not_alaogluErdosConjecture hfail
    have hhalf : (0 : ℝ) < c / 2 := by linarith
    obtain ⟨T, hTlt, hT1⟩ :=
      ((hfreq (c / 2) hhalf).and_eventually (eventually_ge_atTop 1)).exists
    have hTR : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT1
    have hpos : 0 < c * (T : ℝ) := mul_pos hc (by linarith)
    have hlow := hbound T
    linarith

/-- **Block-growth reformulations.**  Packaging of the four equivalent block-growth forms of
the Alaoglu--Erdős conjecture: boundedness, `o(T)`, vanishing lower density, and the exact
value `1`. -/
theorem alaogluErdosConjecture_block_growth_reformulations :
    (AlaogluErdosConjecture ↔ ∃ C : ℕ, ∀ T : ℕ, dyadicBlockCount T ≤ C) ∧
      (AlaogluErdosConjecture ↔
        (fun T : ℕ ↦ (dyadicBlockCount T : ℝ)) =o[atTop] fun T : ℕ ↦ (T : ℝ)) ∧
      (AlaogluErdosConjecture ↔
        ∀ ε : ℝ, 0 < ε → ∃ᶠ T : ℕ in atTop, (dyadicBlockCount T : ℝ) < ε * (T : ℝ)) ∧
      (AlaogluErdosConjecture ↔ ∀ T : ℕ, dyadicBlockCount T = 1) :=
  ⟨alaogluErdosConjecture_iff_dyadicBlock_bounded,
    alaogluErdosConjecture_iff_dyadicBlock_isLittleO,
    alaogluErdosConjecture_iff_dyadicBlock_liminf_zero,
    alaogluErdosConjecture_iff_dyadicBlock_eq_one⟩

end

end LeanProofs.TwoBaseIntegerExponent
