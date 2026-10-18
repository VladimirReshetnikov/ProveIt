import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs15ExplicitThresholds
import GowersSzemeredi.Proofs16SinglePieceGlobalSide
import GowersSzemeredi.Proofs16PolyPieceTwoDataSide
import GowersSzemeredi.Proofs16PolyPieceTwoSide
import GowersSzemeredi.Proofs16ShortScaleSide

/-! Declarations of `Proofs16PolyCoverTwo` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- The number of pieces: `⌊γ⁻²/(5θ′)⌋`. -/
def polyTwoPieces (gamma theta : Real) : Nat :=
  ⌊gamma ^ (-(2 : Int)) / (5 * polyPieceBudget theta gamma)⌋₊

/-- The graph count of the family cover for a relation. -/
def polyTwoFamCount (theta gamma : Real) : Real → Real :=
  fun rho => max (famPieceGraphBound (famTwoQr (polyTwoPieces gamma theta) (polyPieceFaceCount theta gamma))
      (famTwoPb (polyTwoPieces gamma theta) (polyPieceFaceCount theta gamma))
      (polyTwoPieces gamma theta) rho)
    ((3 ^ (1 + 1) * polyTwoPieces gamma theta : Nat) : Real)

/-- The width exponent of the family cover for a relation. -/
def polyTwoFamExp (A Bq : Nat → Real) (theta gamma : Real) : Real → Real :=
  fun rho =>
    let m := polyTwoPieces gamma theta
    let qs := polyPieceSpecCount theta gamma
    let qf := polyPieceFaceCount theta gamma
    section16CappedWidthExponent
      (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qf) rho *
        famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho / 4)
      (section16RoundedPowerThreshold (pieceWidthScale A (famTwoQb m qs) (section16Zeta theta gamma 1) rho)
        (pieceLineExponent Bq (famTwoQb m qs) (famTwoEb m qs) (famTwoEr m qf) rho)
        (famPieceSliceExponent (famTwoQr m qf) (famTwoEs m qf) m rho))

/-! ### `PolyCoverAt 2` -/

theorem polyTwoFamExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} {rho : Real} (hrho : 0 < rho) :
    0 < polyTwoFamExp A Bq theta gamma rho := by
  unfold polyTwoFamExp
  exact famTwoCappedExponent_pos hB hrho

end

end LeanProofs.GowersSzemeredi

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- Lemma 15.6's modulus threshold at `β = θ/2`, and at least `3`. -/
def polyTwoThreshold (theta gamma : Real) : Real :=
  max 3 (lemma156ExplicitThreshold 1 (theta / 2) gamma)

/-! ### The extraction step and the large-modulus cover -/

/-- Every sub-relation with a large projection contains a piece. -/
theorem section16_poly_piece_two_of_subrelation
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoThreshold theta gamma ≤ N)
    {Gamma : Finset (Point N 2 × ZMod N)} (hprod : RelationProductProperty gamma Gamma)
    (Delta : Finset (Point N 2 × ZMod N)) (hDelta : Delta ⊆ Gamma)
    (hproj : theta * (N : Real) ^ 2 ≤ (relationProjection Delta).card) :
    Nonempty (PolyPieceTwoData Delta (section16Zeta theta gamma 1)
      (5 * polyPieceBudget theta gamma) (polyPieceSpecCount theta gamma)
      (polyPieceFaceCount theta gamma) (polyPieceFaceCount theta gamma)) := by
  -- a selection
  let phi : Point N 2 → ZMod N := fun x =>
    if h : ∃ y, (x, y) ∈ Delta then Classical.choose h else 0
  have hsel : GraphContained (relationProjection Delta) phi Delta := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hex : ∃ y, (z.1, y) ∈ Delta := ⟨z.2, by simpa using hz⟩
    simp only [phi, dif_pos hex]
    exact Classical.choose_spec hex
  have hprodB : HasProductProperty (relationProjection Delta) phi gamma :=
    (RelationProductProperty.mono hprod hDelta) _ phi hsel
  -- Lemma 15.6 at β = θ/2
  have hN3 : (3 : Real) ≤ N := (le_max_left _ _).trans hN
  have hNthr : lemma156ExplicitThreshold 1 (theta / 2) gamma ≤ N := (le_max_right _ _).trans hN
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2
    rw [h2] at hN3
    norm_num at hN3)
  have hβ : theta / 2 * (N : Real) ^ (1 + 1) ≤ (relationProjection Delta).card := by
    have : (0 : Real) ≤ (N : Real) ^ 2 := by positivity
    rw [show (1 + 1 : Nat) = 2 from rfl]
    nlinarith
  obtain ⟨B', hB'sub, harr1, harr2⟩ := lemma_15_6_of_density_lower_explicit 1 (theta / 2) gamma
    le_rfl (by positivity) (by linarith) hg hg1 N hNthr hprime hodd
    (relationProjection Delta) phi hβ hprodB
  have hθ1 : section16ThetaOne theta gamma 1 = (theta / 2 * gamma / 2) ^ (2 ^ (2 ^ (1 + 5))) := by
    unfold section16ThetaOne
    congr 1
    ring
  have hBarr : section16ThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤
        generalArrangementCount 8 B' ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B' ≤
        respectedGeneralArrangementCount 8 B' phi := by
    refine ⟨?_, ?_⟩
    · rw [hθ1]; exact harr1
    · rw [two_rpow_neg_44]; exact harr2
  have hgraph : partialGraph B' phi ⊆ Delta := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hsel x (hB'sub hx)
  exact section16_poly_piece_two_data ht ht1 hg hg1 Delta B' phi hgraph hBarr
    (hprodB.mono hB'sub)

/-- **The large-modulus cover of a relation.** -/
theorem section16_poly_cover_two_large {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoThreshold theta gamma ≤ N)
    (Gamma : Finset (Point N 2 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2)
    (hprod : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
      MultiplyLinearWith (polyTwoFamCount theta gamma) (polyTwoFamExp A Bq theta gamma)
        (restrictRelation Gamma J) := by
  obtain ⟨hθ₂pos, _⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hmass : 0 < 5 * polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
  obtain ⟨J, hJ, P, hcov⟩ := section16_poly_piece_two_decomposition_of_extract hmass Gamma hsize
    (fun Delta hDelta hproj =>
      section16_poly_piece_two_of_subrelation ht ht1 hg hg1 hN hprod Delta hDelta hproj)
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  exact ⟨J, hJ, MultiplyLinearWith.subset
    (section16_poly_family_two_cover hA hB hlemma6 hz hzHalf P) hcov⟩

/-- The count control of `PolyCoverAt 2`. -/
def polyTwoQb (gamma theta : Real) : Real → Real :=
  fun rho => max (polyTwoFamCount theta gamma rho)
    ((3 ^ 2 * ⌈polyTwoThreshold theta gamma⌉₊ : Nat) : Real)

/-- The width-exponent control of `PolyCoverAt 2`. -/
def polyTwoEb (A Bq : Nat → Real) (gamma theta : Real) : Real → Real :=
  fun rho => section16CappedWidthExponent (polyTwoFamExp A Bq theta gamma rho)
    (polyTwoThreshold theta gamma)

/-- **`PolyCoverAt 2`**, from the family Lemma 16.6 at a power width. -/
theorem polyCoverAt_two_of_family_lemma6 {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq)) :
    PolyCoverAt 2 polyTwoQb (polyTwoEb A Bq) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  by_cases hN : polyTwoThreshold theta gamma ≤ N
  · obtain ⟨J, hJ, hML⟩ := section16_poly_cover_two_large hA hB hlemma6 ht ht1 hg hg1 hN
      Gamma hsize hprod
    refine ⟨J, hJ, MultiplyLinearWith.weaken hML (fun s _ _ => le_max_left _ _) ?_ ?_⟩
    · intro s hs _
      exact section16CappedWidthExponent_pos (polyTwoFamExp_pos hB hs)
    · intro s _ _
      exact min_le_left _ _
  · have hNlt : (N : Real) < polyTwoThreshold theta gamma := lt_of_not_ge hN
    refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : ((Finset.univ : Finset (Point N 2)).card : Real) = (N : Real) ^ 2 := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ 2 := by positivity
      nlinarith
    · exact multiplyLinearWith_of_small_modulus (by norm_num : 0 < 2) hNlt
        (restrictRelation Gamma Finset.univ)
        (polyTwoFamCount theta gamma) (polyTwoFamExp A Bq theta gamma)
        (fun s hs _ => polyTwoFamExp_pos hB hs)

end

end LeanProofs.GowersSzemeredi
