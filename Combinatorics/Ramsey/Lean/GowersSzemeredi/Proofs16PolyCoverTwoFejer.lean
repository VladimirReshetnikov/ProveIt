import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs16TightRadius

/-! **`PolyCoverAt 2` with the Fejér θ₁ and the tight Bohr radius**
(Notes L.16d).

The dimension-two cover (`polyCoverAt_two_of_family_lemma6`) seeds the
split-class recursion. Here it is built with:
* the Fejér Lemma 15.6 at `k = 1` (`fejer_product_of_density_lower_explicit`)
  in place of the printed one, so the arrangement density is
  `fejerThetaOne θ γ 1 = (θγ/4)^(fejerProductExponent 1)`;
* the tight radius `tightZeta (θ₁′/4)` in place of `section16Zeta θ γ 1`;
* the pieces of `section16_poly_piece_two_data_with`.

Everything else (the greedy peeling, the padding to
`polyTwoFejerPieces = ⌊γ⁻²/(5θ′)⌋`, the simultaneous family cover, and the
coarse cover below the threshold) is the corpus proof, copied by a script.
The family Lemma 16.6 input is the generic `AbstractFamilyLemma166At 1`,
unchanged.

`polyCoverAt_two_fejer_of_family_lemma6`, `polyTwoFejerEb`,
`polyTwoFejerFamCount`, `polyTwoFejerFamExp`, `polyTwoFejerFamExp_pos`,
`polyTwoFejerQb` and `section16_poly_cover_two_large_fejer` are in
`Proofs16PolyCoverTwoFejerSide`, outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The Fejér arrangement density at dimension one lies in `(0, 1/36]` after
division by `4`. -/
theorem fejerThetaOne_one_bounds {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < fejerThetaOne theta gamma 1 / 4 ∧ fejerThetaOne theta gamma 1 / 4 ≤ 1 / 36 := by
  have hp : 0 < theta * gamma / 4 := by positivity
  have hp1 : theta * gamma / 4 ≤ 1 / 4 := by nlinarith
  have hE : 2 ≤ fejerProductExponent 1 := by
    unfold fejerProductExponent fejerSelectionExponent; norm_num
  refine ⟨by unfold fejerThetaOne; positivity, ?_⟩
  have h : fejerThetaOne theta gamma 1 ≤ (1 / 4 : Real) ^ 2 := by
    unfold fejerThetaOne
    calc (theta * gamma / 4) ^ fejerProductExponent 1
        ≤ (1 / 4 : Real) ^ fejerProductExponent 1 := pow_le_pow_left₀ hp.le hp1 _
      _ ≤ (1 / 4 : Real) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hE
  norm_num at h ⊢
  linarith

/-- The tight radius is positive and at most `1/2`. -/
theorem tightZeta_pos_le_half {a : Real} (ha : 0 < a) (ha1 : a ≤ 1) :
    0 < tightZeta a ∧ tightZeta a ≤ 1 / 2 := by
  unfold tightZeta
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  have hs : 1 ≤ tightRadiusExponent a := by
    unfold tightRadiusExponent
    rw [le_div_iff₀ (pow_pos ha 11)]
    have h1 : a ^ 11 ≤ 1 := pow_le_one₀ ha.le ha1
    nlinarith
  calc (2 : Real) ^ (-tightRadiusExponent a) ≤ (2 : Real) ^ (-(1 : Real)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num

/-! ### Parameters -/

/-- The Fejér Lemma 15.6's modulus threshold at `β = θ/2`, and at least `3`. -/
def polyTwoFejerThreshold (theta gamma : Real) : Real :=
  max 3 (fejerProductThreshold 1 (theta / 2) gamma)

/-- The number of pieces: `⌊γ⁻²/(5θ′)⌋`. -/
def polyTwoFejerPieces (gamma theta : Real) : Nat :=
  ⌊gamma ^ (-(2 : Int)) / (5 * polyPieceBudgetW (fejerThetaOne theta gamma 1))⌋₊

/-! ### The extraction step and the large-modulus cover -/

/-- Every sub-relation with a large projection contains a piece. -/
theorem section16_poly_piece_two_of_subrelation_fejer
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoFejerThreshold theta gamma ≤ N)
    {Gamma : Finset (Point N 2 × ZMod N)} (hprod : RelationProductProperty gamma Gamma)
    (Delta : Finset (Point N 2 × ZMod N)) (hDelta : Delta ⊆ Gamma)
    (hproj : theta * (N : Real) ^ 2 ≤ (relationProjection Delta).card) :
    Nonempty (PolyPieceTwoData Delta (tightZeta (fejerThetaOne theta gamma 1 / 4))
      (5 * polyPieceBudgetW (fejerThetaOne theta gamma 1)) (polyPieceSpecCountW (fejerThetaOne theta gamma 1))
      (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma) (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma)) := by
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
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  -- the Fejér Lemma 15.6 at β = θ/2
  have hN3 : (3 : Real) ≤ N := (le_max_left _ _).trans hN
  have hNthr : fejerProductThreshold 1 (theta / 2) gamma ≤ N := (le_max_right _ _).trans hN
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2
    rw [h2] at hN3
    norm_num at hN3)
  have hβ : theta / 2 * (N : Real) ^ (1 + 1) ≤ (relationProjection Delta).card := by
    have : (0 : Real) ≤ (N : Real) ^ 2 := by positivity
    rw [show (1 + 1 : Nat) = 2 from rfl]
    nlinarith
  obtain ⟨B', hB'sub, harr1, harr2⟩ := fejer_product_of_density_lower_explicit 1 (theta / 2) gamma
    le_rfl (by positivity) (by linarith) hg hg1 N hNthr hprime hodd
    (relationProjection Delta) phi hβ hprodB
  have hθ1 : fejerThetaOne theta gamma 1 = (theta / 2 * gamma / 2) ^ fejerProductExponent 1 := by
    unfold fejerThetaOne
    congr 1
    ring
  have hBarr : fejerThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤
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
  exact section16_poly_piece_two_data_with hfa0 hfaS (tightZeta_condition hfa0)
    (tightZeta_pos_le_half hfa0 (by linarith)).1 hg hg1 Delta B' phi hgraph hBarr
    (hprodB.mono hB'sub)

end LeanProofs.GowersSzemeredi
