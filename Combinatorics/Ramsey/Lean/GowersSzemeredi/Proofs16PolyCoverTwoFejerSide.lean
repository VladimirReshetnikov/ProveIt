import GowersSzemeredi.Proofs16PolyCoverTwoFejer

/-! Declarations of `Proofs16PolyCoverTwoFejer` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- The graph count of the family cover for a relation. -/
def polyTwoFejerFamCount (theta gamma : Real) : Real → Real :=
  fun rho => max (famPieceGraphBound (famTwoQr (polyTwoFejerPieces gamma theta) (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma))
      (famTwoPb (polyTwoFejerPieces gamma theta) (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma))
      (polyTwoFejerPieces gamma theta) rho)
    ((3 ^ (1 + 1) * polyTwoFejerPieces gamma theta : Nat) : Real)

/-- The width exponent of the family cover for a relation. -/
def polyTwoFejerFamExp (A Bq : Nat → Real) (theta gamma : Real) : Real → Real :=
  fun rho =>
    let m := polyTwoFejerPieces gamma theta
    let qs := polyPieceSpecCountW (fejerThetaOne theta gamma 1)
    let qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma
    section16CappedWidthExponent
      (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qf) rho *
        famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho / 4)
      (section16RoundedPowerThreshold (pieceWidthScale A (famTwoQb m qs) (tightZeta (fejerThetaOne theta gamma 1 / 4)) rho)
        (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qf) rho)
        (famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho))

/-- **The large-modulus cover of a relation.** -/
theorem section16_poly_cover_two_large_fejer {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoFejerThreshold theta gamma ≤ N)
    (Gamma : Finset (Point N 2 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2)
    (hprod : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
      MultiplyLinearWith (polyTwoFejerFamCount theta gamma) (polyTwoFejerFamExp A Bq theta gamma)
        (restrictRelation Gamma J) := by
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hθ₂pos, _⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  have hmass : 0 < 5 * polyPieceBudgetW (fejerThetaOne theta gamma 1) := by
    unfold polyPieceBudgetW; positivity
  obtain ⟨J, hJ, P, hcov⟩ := section16_poly_piece_two_decomposition_of_extract hmass Gamma hsize
    (fun Delta hDelta hproj =>
      section16_poly_piece_two_of_subrelation_fejer ht ht1 hg hg1 hN hprod Delta hDelta hproj)
  obtain ⟨hz, hzHalf⟩ := tightZeta_pos_le_half hfa0 (by linarith)
  exact ⟨J, hJ, MultiplyLinearWith.subset
    (section16_poly_family_two_cover hA hB hlemma6 hz hzHalf P) hcov⟩

/-! ### `PolyCoverAt 2` -/

/-- The count control of `PolyCoverAt 2`. -/
def polyTwoFejerQb (gamma theta : Real) : Real → Real :=
  fun rho => max (polyTwoFejerFamCount theta gamma rho)
    ((3 ^ 2 * ⌈polyTwoFejerThreshold theta gamma⌉₊ : Nat) : Real)

/-- The width-exponent control of `PolyCoverAt 2`. -/
def polyTwoFejerEb (A Bq : Nat → Real) (gamma theta : Real) : Real → Real :=
  fun rho => section16CappedWidthExponent (polyTwoFejerFamExp A Bq theta gamma rho)
    (polyTwoFejerThreshold theta gamma)

theorem polyTwoFejerFamExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} {rho : Real} (hrho : 0 < rho) :
    0 < polyTwoFejerFamExp A Bq theta gamma rho := by
  unfold polyTwoFejerFamExp
  exact famTwoCappedExponent_pos hB hrho

/-- **`PolyCoverAt 2`**, from the family Lemma 16.6 at a power width. -/
theorem polyCoverAt_two_fejer_of_family_lemma6 {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq)) :
    PolyCoverAt 2 polyTwoFejerQb (polyTwoFejerEb A Bq) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  by_cases hN : polyTwoFejerThreshold theta gamma ≤ N
  · obtain ⟨J, hJ, hML⟩ := section16_poly_cover_two_large_fejer hA hB hlemma6 ht ht1 hg hg1 hN
      Gamma hsize hprod
    refine ⟨J, hJ, MultiplyLinearWith.weaken hML (fun s _ _ => le_max_left _ _) ?_ ?_⟩
    · intro s hs _
      exact section16CappedWidthExponent_pos (polyTwoFejerFamExp_pos hB hs)
    · intro s _ _
      exact min_le_left _ _
  · have hNlt : (N : Real) < polyTwoFejerThreshold theta gamma := lt_of_not_ge hN
    refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : ((Finset.univ : Finset (Point N 2)).card : Real) = (N : Real) ^ 2 := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ 2 := by positivity
      nlinarith
    · exact multiplyLinearWith_of_small_modulus (by norm_num : 0 < 2) hNlt
        (restrictRelation Gamma Finset.univ)
        (polyTwoFejerFamCount theta gamma) (polyTwoFejerFamExp A Bq theta gamma)
        (fun s hs _ => polyTwoFejerFamExp_pos hB hs)

end

end LeanProofs.GowersSzemeredi
