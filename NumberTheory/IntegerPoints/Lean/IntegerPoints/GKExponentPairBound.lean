import IntegerPoints.GKProcessWords

/-!
# The bound component of an exponent pair

`SatisfiesExponentPairBound k l` is exactly the analytic-bound component of
`IsExponentPair k l`; the latter additionally records the four conventional
coordinate restrictions.  This module exposes that definitional relationship
and projects the proved elementary pairs and the `A`- and `B`-processes to the
bound-only interface.
-/

namespace LeanProofs.IntegerPoints

/-- An exponent pair consists exactly of its four coordinate restrictions and
its uniform exponential-sum bound. -/
theorem isExponentPair_iff_coordinates_and_bound (k l : ℝ) :
    IsExponentPair k l ↔
      0 ≤ k ∧ k ≤ 1 / 2 ∧ 1 / 2 ≤ l ∧ l ≤ 1 ∧
        SatisfiesExponentPairBound k l := by
  rfl

/-- Every exponent pair satisfies its underlying exponential-sum bound. -/
theorem satisfiesExponentPairBound_of_isExponentPair {k l : ℝ}
    (h : IsExponentPair k l) : SatisfiesExponentPairBound k l :=
  h.2.2.2.2

/-- The bound component and the four conventional coordinate restrictions
assemble into an exponent pair. -/
theorem isExponentPair_of_coordinates_and_bound {k l : ℝ}
    (hk₀ : 0 ≤ k) (hk₁ : k ≤ 1 / 2) (hl₀ : 1 / 2 ≤ l) (hl₁ : l ≤ 1)
    (hbound : SatisfiesExponentPairBound k l) : IsExponentPair k l :=
  ⟨hk₀, hk₁, hl₀, hl₁, hbound⟩

/-- The trivial pair `(0, 1)` satisfies the exponent-pair bound. -/
theorem satisfiesExponentPairBound_zero_one : SatisfiesExponentPairBound 0 1 :=
  satisfiesExponentPairBound_of_isExponentPair isExponentPair_zero_one

/-- The pair `(1/2, 1/2)` satisfies the exponent-pair bound. -/
theorem satisfiesExponentPairBound_half_half :
    SatisfiesExponentPairBound (1 / 2) (1 / 2) :=
  satisfiesExponentPairBound_of_isExponentPair isExponentPair_half_half

/-- The pair `(1/6, 2/3)` satisfies the exponent-pair bound. -/
theorem satisfiesExponentPairBound_sixth_two_thirds :
    SatisfiesExponentPairBound (1 / 6) (2 / 3) :=
  satisfiesExponentPairBound_of_isExponentPair AP.isExponentPair_sixth_two_thirds

/-- The `A`-transform of an exponent pair satisfies the transformed bound. -/
theorem satisfiesExponentPairBound_A {k l : ℝ} (h : IsExponentPair k l) :
    SatisfiesExponentPairBound
      (k / (2 * k + 2)) ((k + l + 1) / (2 * k + 2)) :=
  satisfiesExponentPairBound_of_isExponentPair (AP.isExponentPair_A h)

/-- The `B`-transform of an exponent pair satisfies the transformed bound. -/
theorem satisfiesExponentPairBound_B {k l : ℝ} (h : IsExponentPair k l) :
    SatisfiesExponentPairBound (l - 1 / 2) (k + 1 / 2) :=
  satisfiesExponentPairBound_of_isExponentPair (gk_theorem310_holds k l h)

/-- Every finite word in the `A`- and `B`-processes, applied to `(0, 1)`,
satisfies the resulting exponent-pair bound. -/
theorem gk_sec31_words_satisfy_exponent_pair_bound :
    ∀ w : List Bool,
      SatisfiesExponentPairBound
        (gk_process_word w (0, 1)).1 (gk_process_word w (0, 1)).2 :=
  fun w => satisfiesExponentPairBound_of_isExponentPair (gk_sec31_words_holds w)

end LeanProofs.IntegerPoints
