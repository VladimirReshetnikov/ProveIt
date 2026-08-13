import KlarnerConstant.GeometricUGeometry

/-!
# The five-branch geometric recurrence for `U`

This module proves the last same-index recurrence in Bui's Appendix B:

`U(n) ≤ (D*H + S*D + Y*R + W*Y)(n) + (U*Z*Z)(n)`.

The local picture is the same two-column, three-row occupancy split used for
`P`, but a `U` occurrence has one additional forbidden cell southwest of the
marked horizontal domino.  That extra exclusion strengthens, branch by
branch, `E,Q,X,V,Y` to `D,S,Y,W,Z`.  In the third branch the left vertical
domino is anchored at its lower cell and rotated clockwise; this is essential:
with the upper anchoring used in the weaker `P` recurrence, the additional
`Y` exclusion would point at an unconstrained cell.

Every branch below retains the actual connected territories furnished by
`SeededPartition`.  The encoders record normalized marked territories and
their positive cardinalities, while the decoders undo normalization,
orientation, and translation.  Their union is exactly the source marked
polyomino, so the global five-way map is genuinely injective.
-/

namespace LeanProofs.KlarnerConstant

open GeometricUInternal

/-! ## The global five-way injection -/

private abbrev UTarget (n : ℕ) :=
  Sum (UMarkedPair .d .h n)
    (Sum (UMarkedPair .s .d n)
      (Sum (UMarkedPair .y .r n)
        (Sum (UMarkedPair .w .y n)
          (UMarkedTriple .u .z .z n))))

private noncomputable def uMarkedMap (n : ℕ) :
    MarkedOccurrence .u n → UTarget n := fun x ↦ by
  let frame : UFrame x.1.toPolyomino x.2.1 :=
    uFrame_of_occursAt (uMarked_occursAt x)
  by_cases h01 : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells
  · by_cases h11 : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells
    · by_cases h02 : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
      · by_cases h12 : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inr
            (uFifthMap x frame h01 h02 h11 h12))))
        · exact Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (uFourthMap x frame h01 h02 h11 h12))))
      · exact Sum.inr (Sum.inr (Sum.inl
          (uThirdMap x frame h01 h11 h02)))
    · exact Sum.inr (Sum.inl (uSecondMap x frame h01 h11))
  · exact Sum.inl (uFirstMap x frame h01)

private theorem uMarkedMap_injective (n : ℕ) :
    Function.Injective (uMarkedMap n) := by
  intro x y hxy
  let fx : UFrame x.1.toPolyomino x.2.1 :=
    uFrame_of_occursAt (uMarked_occursAt x)
  let fy : UFrame y.1.toPolyomino y.2.1 :=
    uFrame_of_occursAt (uMarked_occursAt y)
  by_cases h01x : pCell x.2.1 0 1 ∈ x.1.toPolyomino.cells
  · by_cases h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells
    · by_cases h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells
      · by_cases h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells
        · by_cases h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
          · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
            · by_cases h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
              · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
                · apply uFifthMap_injective x y fx fy h01x h01y h02x h02y
                      h11x h11y h12x h12y
                  simpa [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] using hxy
                · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] at hxy
              · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
                · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] at hxy
                · apply uFourthMap_injective x y fx fy h01x h01y h02x h02y
                      h11x h11y h12x h12y
                  simpa [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                    h02x, h02y, h12x, h12y] using hxy
            · by_cases h12x :
                  pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
              · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12x] at hxy
              · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12x] at hxy
          · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
            · by_cases h12y :
                  pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
              · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12y] at hxy
              · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                  h02x, h02y, h12y] at hxy
            · apply uThirdMap_injective x y fx fy h01x h01y h11x h11y
                  h02x h02y
              simpa [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02x, h02y] using hxy
        · by_cases h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
          · by_cases h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
            · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02x, h12x] at hxy
            · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02x, h12x] at hxy
          · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
              h02x] at hxy
      · by_cases h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells
        · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
          · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
            · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02y, h12y] at hxy
            · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
                h02y, h12y] at hxy
          · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y,
              h02y] at hxy
        · apply uSecondMap_injective x y fx fy h01x h01y h11x h11y
          simpa [uMarkedMap, fx, fy, h01x, h01y, h11x, h11y] using hxy
    · by_cases h11x : pCell x.2.1 1 1 ∈ x.1.toPolyomino.cells
      · by_cases h02x : pCell x.2.1 0 2 ∈ x.1.toPolyomino.cells
        · by_cases h12x : pCell x.2.1 1 2 ∈ x.1.toPolyomino.cells
          · simp [uMarkedMap, fx, fy, h01x, h01y, h11x,
              h02x, h12x] at hxy
          · simp [uMarkedMap, fx, fy, h01x, h01y, h11x,
              h02x, h12x] at hxy
        · simp [uMarkedMap, fx, fy, h01x, h01y, h11x, h02x] at hxy
      · simp [uMarkedMap, fx, fy, h01x, h01y, h11x] at hxy
  · by_cases h01y : pCell y.2.1 0 1 ∈ y.1.toPolyomino.cells
    · by_cases h11y : pCell y.2.1 1 1 ∈ y.1.toPolyomino.cells
      · by_cases h02y : pCell y.2.1 0 2 ∈ y.1.toPolyomino.cells
        · by_cases h12y : pCell y.2.1 1 2 ∈ y.1.toPolyomino.cells
          · simp [uMarkedMap, fx, fy, h01x, h01y, h11y,
              h02y, h12y] at hxy
          · simp [uMarkedMap, fx, fy, h01x, h01y, h11y,
              h02y, h12y] at hxy
        · simp [uMarkedMap, fx, fy, h01x, h01y, h11y, h02y] at hxy
      · simp [uMarkedMap, fx, fy, h01x, h01y, h11y] at hxy
    · apply uFirstMap_injective x y fx fy h01x h01y
      simpa [uMarkedMap, fx, fy, h01x, h01y] using hxy

/-! ## Cardinal arithmetic and the unconditional recurrence -/

private theorem uAggregate_zero (kind : BuiNeighborhood) :
    kind.aggregateOccurrenceCount 0 = 0 := by
  classical
  unfold BuiNeighborhood.aggregateOccurrenceCount
  apply Finset.sum_eq_zero
  intro P _
  have hpos : 0 < P.toPolyomino.cells.card :=
    Finset.card_pos.mpr P.toPolyomino.nonempty
  rw [P.card_cells] at hpos
  omega

private theorem uCard_markedOccurrence (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) =
      kind.aggregateOccurrenceCount n := by
  classical
  simp [MarkedOccurrence, BuiNeighborhood.aggregateOccurrenceCount,
    BuiNeighborhood.occurrenceCount, OffsetPattern.occurrenceCount]

private noncomputable def uPositiveAggregate (kind : BuiNeighborhood) : ℕ → ℕ
  | 0 => 0
  | n + 1 => kind.aggregateOccurrenceCount (n + 1)

private theorem uCard_markedOccurrence_eq_positiveAggregate
    (kind : BuiNeighborhood) (n : ℕ) :
    Fintype.card (MarkedOccurrence kind n) = uPositiveAggregate kind n := by
  cases n with
  | zero =>
      rw [uCard_markedOccurrence, uAggregate_zero]
      rfl
  | succ n =>
      rw [uCard_markedOccurrence]
      rfl

/-- Natural cardinal of a positive-index two-factor target used in the `U`
decomposition. -/
noncomputable def buiUPairAggregateCount
    (left right : BuiNeighborhood) (n : ℕ) : ℕ :=
  ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
    uPositiveAggregate left ij.1 * uPositiveAggregate right ij.2

/-- Natural cardinal of the positive-index left-associated three-factor
target used in the `U` decomposition. -/
noncomputable def buiUTripleAggregateCount
    (first second third : BuiNeighborhood) (n : ℕ) : ℕ :=
  ∑ outer ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
    buiUPairAggregateCount first second outer.1 *
      uPositiveAggregate third outer.2

private theorem uCard_markedPair
    (left right : BuiNeighborhood) (n : ℕ) :
    Fintype.card (UMarkedPair left right n) =
      buiUPairAggregateCount left right n := by
  classical
  change Fintype.card
      (Σ ij : UAntidiagonalIndex n,
        MarkedOccurrence left ij.1.1 × MarkedOccurrence right ij.1.2) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,
    uCard_markedOccurrence_eq_positiveAggregate]
  rw [Finset.univ_eq_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)]
  unfold buiUPairAggregateCount
  exact Finset.sum_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)
    (fun ij => uPositiveAggregate left ij.1 * uPositiveAggregate right ij.2)

private theorem uCard_markedTriple
    (first second third : BuiNeighborhood) (n : ℕ) :
    Fintype.card (UMarkedTriple first second third n) =
      buiUTripleAggregateCount first second third n := by
  classical
  change Fintype.card
      (Σ outer : UAntidiagonalIndex n,
        UMarkedPair first second outer.1.1 ×
          MarkedOccurrence third outer.1.2) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod,
    uCard_markedPair, uCard_markedOccurrence_eq_positiveAggregate]
  rw [Finset.univ_eq_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)]
  unfold buiUTripleAggregateCount
  exact Finset.sum_attach
    (Finset.Nat.instHasAntidiagonal.antidiagonal n)
    (fun outer => buiUPairAggregateCount first second outer.1 *
      uPositiveAggregate third outer.2)

private theorem cauchyTwo_coefficient_eq_buiUPairAggregateCount
    (left right : BuiNeighborhood) (n : ℕ) :
    cauchyTwo left.coefficient right.coefficient n =
      (buiUPairAggregateCount left right n : ℚ) := by
  classical
  unfold cauchyTwo buiUPairAggregateCount BuiNeighborhood.coefficient
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [Nat.cast_mul]
  congr 1
  · cases ij.1 <;> simp [positivePart, uPositiveAggregate]
  · cases ij.2 <;> simp [positivePart, uPositiveAggregate]

private theorem cauchyThree_coefficient_eq_buiUTripleAggregateCount
    (first second third : BuiNeighborhood) (n : ℕ) :
    cauchyThree first.coefficient second.coefficient third.coefficient n =
      (buiUTripleAggregateCount first second third n : ℚ) := by
  classical
  change (∑ outer ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
      positivePart (cauchyTwo first.coefficient second.coefficient) outer.1 *
        positivePart third.coefficient outer.2) = _
  unfold buiUTripleAggregateCount
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro outer houter
  rw [Nat.cast_mul]
  congr 1
  · cases outer.1 with
    | zero => simp [positivePart, buiUPairAggregateCount, uPositiveAggregate]
    | succ m =>
        simp only [positivePart_succ]
        exact cauchyTwo_coefficient_eq_buiUPairAggregateCount
          first second (m + 1)
  · cases outer.2 <;>
      simp [positivePart, uPositiveAggregate, BuiNeighborhood.coefficient]

/-- The local cardinal presentation is extensionally the shared two-factor
aggregate count from `GeometricPPartition`. -/
theorem buiUPairAggregateCount_eq_buiPairAggregateCount
    (left right : BuiNeighborhood) (n : ℕ) :
    buiUPairAggregateCount left right n =
      buiPairAggregateCount left right n := by
  have hu := cauchyTwo_coefficient_eq_buiUPairAggregateCount left right n
  have hp := cauchyTwo_coefficient_eq_buiPairAggregateCount left right n
  exact Nat.cast_injective (R := ℚ) (hu.symm.trans hp)

/-- Likewise, the local three-factor cardinal is the shared three-factor
aggregate count. -/
theorem buiUTripleAggregateCount_eq_buiTripleAggregateCount
    (first second third : BuiNeighborhood) (n : ℕ) :
    buiUTripleAggregateCount first second third n =
      buiTripleAggregateCount first second third n := by
  have hu := cauchyThree_coefficient_eq_buiUTripleAggregateCount
    first second third n
  have hp := cauchyThree_coefficient_eq_buiTripleAggregateCount
    first second third n
  exact Nat.cast_injective (R := ℚ) (hu.symm.trans hp)

private theorem uCard_target (n : ℕ) :
    Fintype.card (UTarget n) =
      buiUPairAggregateCount .d .h n +
      buiUPairAggregateCount .s .d n +
      buiUPairAggregateCount .y .r n +
      buiUPairAggregateCount .w .y n +
      buiUTripleAggregateCount .u .z .z n := by
  simp only [UTarget, Fintype.card_sum, uCard_markedPair,
    uCard_markedTriple]
  omega

/-- The natural-number marked-occurrence form of Bui's five-branch `U`
recurrence, proved by a lossless finite geometric decomposition. -/
theorem buiU_aggregateOccurrenceCount_le (n : ℕ) :
    BuiNeighborhood.u.aggregateOccurrenceCount n ≤
      buiUPairAggregateCount .d .h n +
      buiUPairAggregateCount .s .d n +
      buiUPairAggregateCount .y .r n +
      buiUPairAggregateCount .w .y n +
      buiUTripleAggregateCount .u .z .z n := by
  rw [← uCard_markedOccurrence, ← uCard_target]
  exact Fintype.card_le_of_injective (uMarkedMap n) (uMarkedMap_injective n)

/-- The same natural-number recurrence stated with the shared convolution
cardinals used by the `P` development. -/
theorem buiU_aggregateOccurrenceCount_le_shared (n : ℕ) :
    BuiNeighborhood.u.aggregateOccurrenceCount n ≤
      buiPairAggregateCount .d .h n +
      buiPairAggregateCount .s .d n +
      buiPairAggregateCount .y .r n +
      buiPairAggregateCount .w .y n +
      buiTripleAggregateCount .u .z .z n := by
  simpa [buiUPairAggregateCount_eq_buiPairAggregateCount,
    buiUTripleAggregateCount_eq_buiTripleAggregateCount] using
      buiU_aggregateOccurrenceCount_le n

/-- The unconditional rational coefficient inequality for the actual
geometric `U` sequence. -/
theorem buiU_coefficient_le (n : ℕ) :
    BuiNeighborhood.u.coefficient n ≤
      cauchyTwo BuiNeighborhood.d.coefficient BuiNeighborhood.h.coefficient n +
      cauchyTwo BuiNeighborhood.s.coefficient BuiNeighborhood.d.coefficient n +
      cauchyTwo BuiNeighborhood.y.coefficient BuiNeighborhood.r.coefficient n +
      cauchyTwo BuiNeighborhood.w.coefficient BuiNeighborhood.y.coefficient n +
      cauchyThree BuiNeighborhood.u.coefficient BuiNeighborhood.z.coefficient
        BuiNeighborhood.z.coefficient n := by
  rw [cauchyTwo_coefficient_eq_buiUPairAggregateCount,
    cauchyTwo_coefficient_eq_buiUPairAggregateCount,
    cauchyTwo_coefficient_eq_buiUPairAggregateCount,
    cauchyTwo_coefficient_eq_buiUPairAggregateCount,
    cauchyThree_coefficient_eq_buiUTripleAggregateCount]
  unfold BuiNeighborhood.coefficient
  exact_mod_cast buiU_aggregateOccurrenceCount_le n

/-- The `u` field required by `GeometricBuiGaps`, discharged directly from
finite polyomino geometry. -/
theorem geometricCoefficientProfile_u_recurrence (n : ℕ) (_hn : 2 ≤ n) :
    geometricCoefficientProfile.u n ≤
      cauchyTwo geometricCoefficientProfile.d geometricCoefficientProfile.h n +
      cauchyTwo geometricCoefficientProfile.s geometricCoefficientProfile.d n +
      cauchyTwo geometricCoefficientProfile.y geometricCoefficientProfile.r n +
      cauchyTwo geometricCoefficientProfile.w geometricCoefficientProfile.y n +
      cauchyThree geometricCoefficientProfile.u geometricCoefficientProfile.z
        geometricCoefficientProfile.z n := by
  simpa [geometricCoefficientProfile] using buiU_coefficient_le n


end LeanProofs.KlarnerConstant
