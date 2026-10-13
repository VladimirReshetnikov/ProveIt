import GowersSzemeredi.Proofs16PolyCoverTwo
import GowersSzemeredi.Proofs16PolyPieceTwoDataWith

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
unchanged. -/
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
    have h2 : (1 : Real) ≤ 2 ^ (83 : Nat) := one_le_pow₀ (by norm_num)
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
  classical
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
    have h := hproj
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
  classical
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  have hθ'pos : 0 < polyPieceBudgetW (fejerThetaOne theta gamma 1) := by
    unfold polyPieceBudgetW; linarith
  set θ' := polyPieceBudgetW (fejerThetaOne theta gamma 1) with hθ'def
  obtain ⟨hz, hzHalf⟩ := tightZeta_pos_le_half hfa0 (by linarith)
  set zeta := tightZeta (fejerThetaOne theta gamma 1 / 4) with hzetadef
  set qs := polyPieceSpecCountW (fejerThetaOne theta gamma 1)
  set qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma
  let Good : Finset (Point N 2 × ZMod N) → Prop := fun G =>
    ∃ P : PolyPieceTwoData Gamma zeta (5 * θ') qs qf qf, G = partialGraph P.D P.phi
  have hmass : 0 < 5 * θ' * (N : Real) ^ 2 := by
    have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  obtain ⟨q, G, J, hG, hq, hJ, hcov⟩ := section16_greedy_relation_decomposition Good theta
    (5 * θ' * (N : Real) ^ 2) hmass Gamma (by
      intro Delta hDelta hproj
      obtain ⟨P⟩ := section16_poly_piece_two_of_subrelation_fejer ht ht1 hg hg1 hN hprod Delta
        hDelta hproj
      refine ⟨partialGraph P.D P.phi, P.graph_sub, ?_, ⟨P.widen hDelta, rfl⟩⟩
      rw [partialGraph_card]
      exact P.card_ge)
  -- the number of pieces
  set m := polyTwoFejerPieces gamma theta with hmdef
  have hqm : q ≤ m := by
    rw [hmdef, polyTwoFejerPieces]
    apply Nat.le_floor
    have hNpos : (0 : Real) < (N : Real) ^ 2 := by
      have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      positivity
    have h1 : (q : Real) * (5 * θ' * (N : Real) ^ 2) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 :=
      hq.trans hsize
    rw [le_div_iff₀ (by positivity)]
    have h2 : (q : Real) * (5 * θ') * (N : Real) ^ 2 ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2 := by
      linarith [h1]
    exact le_of_mul_le_mul_right h2 hNpos
  choose P hPG using fun i => (hG i).2
  let Q : Fin m → PolyPieceTwoData Gamma zeta 0 qs qf qf := fun j =>
    if h : j.val < q then (P ⟨j.val, h⟩).toMassZero else PolyPieceTwoData.empty Gamma zeta qs qf qf
  have hfam := section16_poly_family_two_cover hA hB hlemma6 hz hzHalf Q
  refine ⟨J, hJ, MultiplyLinearWith.subset hfam ?_⟩
  intro z hz'
  have hz1 := hcov hz'
  unfold section16FinsetUnion at hz1
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz1
  rw [hPG i] at hi
  refine Finset.mem_biUnion.mpr ⟨⟨i.val, i.isLt.trans_le hqm⟩, Finset.mem_univ _, ?_⟩
  simp only [Q, dif_pos i.isLt]
  exact hi


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
  classical
  by_cases hN : polyTwoFejerThreshold theta gamma ≤ N
  · obtain ⟨J, hJ, hML⟩ := section16_poly_cover_two_large_fejer hA hB hlemma6 ht ht1 hg hg1 hN
      Gamma hsize hprod
    refine ⟨J, hJ, MultiplyLinearWith.weaken hML (fun s _ _ => le_max_left _ _) ?_ ?_⟩
    · intro s hs hs1
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
    · have hfib : ∀ x : Point N 2,
          ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤
            ⌈polyTwoFejerThreshold theta gamma⌉₊ := by
        intro x
        have h1 : ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤ N := by
          refine (Finset.card_le_card_of_injOn (fun z => z.2) (fun _ _ => Finset.mem_univ _)
            ?_).trans (by simp [ZMod.card])
          intro z hz z' hz' h
          exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) h
        refine h1.trans ?_
        have : (N : Real) ≤ ⌈polyTwoFejerThreshold theta gamma⌉₊ :=
          hNlt.le.trans (Nat.le_ceil _)
        exact_mod_cast this
      have hcov := multiplyLinearWith_of_large_box_covers (by norm_num : 0 < 2)
        (Gamma := restrictRelation Gamma Finset.univ) ⌈polyTwoFejerThreshold theta gamma⌉₊ hfib
        (polyTwoFejerFamCount theta gamma) (polyTwoFejerFamExp A Bq theta gamma)
        (fun _ => polyTwoFejerThreshold theta gamma)
        (fun s hs hs1 => polyTwoFejerFamExp_pos hB hs) (by
          intro s _ _ P hP hlarge
          exfalso
          have hw : (P.width : Real) ≤ N := by exact_mod_cast P.width_le_modulus hP
          linarith)
      exact hcov

end LeanProofs.GowersSzemeredi
