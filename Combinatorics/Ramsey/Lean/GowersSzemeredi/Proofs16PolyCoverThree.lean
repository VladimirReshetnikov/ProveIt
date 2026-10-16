import GowersSzemeredi.Proofs16PolyPieceThreeData
import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs05Corollary58

/-! **`PolyCoverAt 3`** (Notes L.5, D4).

The polynomial global-to-local cover of every three-dimensional relation with
the product property. It is assembled exactly as `PolyCoverAt 2`:
* every sub-relation with projection at least `θN³` yields a piece. A
  selection inherits the product property, Lemma 15.6 at `k = 2` and
  `β = θ/2` gives the arrangement conditions, and
  `section16_poly_piece_three_data` gives the piece with its data;
* the greedy decomposition peels pieces of mass `3θ′N³`, padded with empty
  pieces to `polyThreePieces γ θ = ⌊γ⁻²/(3θ′)⌋`;
* the simultaneous cover `section16_poly_family_three_cover`;
* below the threshold `polyThreeThreshold θ γ`, the coarse cover, whose
  large-box premise is vacuous.

The inputs are the abstract family Lemma 16.6 in dimension two, at a width
`section16PowerWidth A₂ Bq₂`, and in dimension one at the explicit power
width of the recurrence constants `K₁, p₁`. The heavy bridge supplies both. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Operations on piece data -/

/-- A piece of a sub-relation is a piece of the relation. -/
def PolyPieceThreeData.widen {N : Nat} [NeZero N] {Gamma Gamma' : Finset (Point N 3 × ZMod N)}
    {zeta mass thS gS thF gF : Real} {q3 : Nat}
    (P : PolyPieceThreeData Gamma' zeta mass thS gS thF gF q3) (hsub : Gamma' ⊆ Gamma) :
    PolyPieceThreeData Gamma zeta mass thS gS thF gF q3 :=
  { P with graph_sub := P.graph_sub.trans hsub }

/-- Forget the mass bound. -/
def PolyPieceThreeData.toMassZero {N : Nat} [NeZero N] {Gamma : Finset (Point N 3 × ZMod N)}
    {zeta mass thS gS thF gF : Real} {q3 : Nat}
    (P : PolyPieceThreeData Gamma zeta mass thS gS thF gF q3) :
    PolyPieceThreeData Gamma zeta 0 thS gS thF gF q3 :=
  { P with card_ge := by simp }

/-- The empty piece. -/
def PolyPieceThreeData.empty {N : Nat} [NeZero N] (Gamma : Finset (Point N 3 × ZMod N))
    (zeta thS gS thF gF : Real) (q3 : Nat) : PolyPieceThreeData Gamma zeta 0 thS gS thF gF q3 where
  D := ∅
  phi := 0
  graph_sub := by
    intro z hz
    simp [partialGraph] at hz
  card_ge := by simp
  H1 := ∅
  K := fun _ => ∅
  A := fun _ => ∅
  f := fun _ _ => 0
  rem := 0
  linear := by intro x hx; simp at hx
  dom := by intro z hz; simp at hz
  ident := by intro z hz; simp at hz
  spec := fun _ => PolyPieceTwoData.empty _ _ _ _ _
  spec_sub := by
    intro z hz
    simp [specRelTwo] at hz
  g1 := 0
  g2 := 0
  g3 := 0
  rem_eq := by intro z hz; simp at hz
  P1 := fun _ => PolyPieceTwoData.empty _ _ _ _ _
  P2 := fun _ => PolyPieceTwoData.empty _ _ _ _ _
  rel1 := by intro z hz; simp at hz
  rel2 := by intro z hz; simp at hz
  rel3 := (relFreimanCover_empty q3).mono (by intro z hz; simp at hz)
  slices := fun _ _ => PolyPieceTwoData.empty _ _ _ _ _
  slices_sub := by
    intro t z hz
    obtain ⟨x, hx, -⟩ := Finset.mem_image.mp hz
    simp [section16FinalCoordinateSection] at hx

/-! ### Parameters -/

/-- The modulus threshold of `PolyCoverAt 3`. -/
def polyThreeThreshold (theta gamma : Real) : Real :=
  max 3 (max (lemma156ExplicitThreshold 2 (theta / 2) gamma) (threeThreshold theta gamma))

/-- The number of pieces: `⌊γ⁻²/(3θ′)⌋`. -/
def polyThreePieces (gamma theta : Real) : Nat :=
  ⌊gamma ^ (-(2 : Int)) / (3 * threeBudget theta gamma)⌋₊

/-- The class of dimension-three pieces of `Γ` at `(θ, γ)`. -/
abbrev PolyPieceThree {N : Nat} [NeZero N] (Gamma : Finset (Point N 3 × ZMod N))
    (theta gamma mass : Real) :=
  PolyPieceThreeData Gamma (section16Zeta theta gamma 2) mass (threeBudget theta gamma)
    (threeDelta theta gamma) (threeBudget theta gamma) gamma (threeFaceCount theta gamma)

/-- The graph count of the family cover of a relation. -/
def polyThreeFamCount (K1 p1 : Nat) (theta gamma : Real) : Real → Real :=
  fun rho => max (famPieceGraphBound
      (famThreeQr (threeBudget theta gamma) gamma (threeFaceCount theta gamma)
        (polyThreePieces gamma theta))
      (famThreePb (threeBudget theta gamma) gamma K1 p1 (polyThreePieces gamma theta))
      (polyThreePieces gamma theta) rho)
    ((3 ^ (2 + 1) * polyThreePieces gamma theta : Nat) : Real)

/-- The width exponent of the family cover of a relation. -/
def polyThreeFamExp (A2 Bq2 : Nat → Real) (K1 p1 : Nat) (theta gamma : Real) : Real → Real :=
  fun rho =>
    let m := polyThreePieces gamma theta
    let tS := threeBudget theta gamma
    let gS := threeDelta theta gamma
    let q3 := threeFaceCount theta gamma
    section16CappedWidthExponent
      (pieceLineExponent Bq2 (famThreeQb tS gS m)
          (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tS gS m)
          (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tS gamma q3 m) rho *
        famPieceSliceExponent (famThreeQr tS gamma q3 m) (famThreeEs tS gamma K1 p1 m) m rho / 4)
      (section16RoundedPowerThreshold
        (pieceWidthScale A2 (famThreeQb tS gS m) (section16Zeta theta gamma 2) rho)
        (pieceLineExponent Bq2 (famThreeQb tS gS m)
          (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tS gS m)
          (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tS gamma q3 m) rho)
        (famPieceSliceExponent (famThreeQr tS gamma q3 m) (famThreeEs tS gamma K1 p1 m) m rho))

/-- The count control of `PolyCoverAt 3`. -/
def polyThreeQb (K1 p1 : Nat) (gamma theta : Real) : Real → Real :=
  fun rho => max (polyThreeFamCount K1 p1 theta gamma rho)
    ((3 ^ 3 * ⌈polyThreeThreshold theta gamma⌉₊ : Nat) : Real)

/-- The width-exponent control of `PolyCoverAt 3`. -/
def polyThreeEb (A2 Bq2 : Nat → Real) (K1 p1 : Nat) (gamma theta : Real) : Real → Real :=
  fun rho => section16CappedWidthExponent (polyThreeFamExp A2 Bq2 K1 p1 theta gamma rho)
    (polyThreeThreshold theta gamma)

theorem polyThreeFamExp_pos {A2 Bq2 : Nat → Real} (hB2 : ∀ q, 0 < Bq2 q) {K1 p1 : Nat}
    (hp1 : 0 < p1) {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) {rho : Real} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    0 < polyThreeFamExp A2 Bq2 K1 p1 theta gamma rho := by
  have hB1 : ∀ q, 0 < familyWidthDivisor 1 p1 q := familyWidthDivisor_pos hp1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 2 ht ht1 hg hg1
  have htS : 0 < threeBudget theta gamma := by unfold threeBudget; positivity
  have htS1 : threeBudget theta gamma ≤ 1 := by unfold threeBudget; linarith
  set m := polyThreePieces gamma theta
  set tS := threeBudget theta gamma
  set gS := threeDelta theta gamma
  set q3 := threeFaceCount theta gamma
  have h8 : 0 < rho / 8 := by positivity
  have h4 : 0 < rho / 4 := by positivity
  have h41 : rho / 4 ≤ 1 := by linarith
  have hEb := uniTwoExp_pos (A := familyWidthPrefactor K1) hB1 (theta := tS) (gamma := gS)
    (m * polyTwoPieces gS tS) h8
  have hEr1 := uniTwoExp_pos (A := familyWidthPrefactor K1) hB1 (theta := tS) (gamma := gamma)
    (m * polyTwoPieces gamma tS) (show 0 < rho / 8 / 4 by positivity)
  have hEr3 := cubicBaseExponent_pos (Nat.succ_pos (m * q3)) (show 0 < rho / 8 / 2 by positivity)
  have hBq := hB2 ⌊famThreeQb tS gS m (rho / 8)⌋₊
  obtain ⟨hr, -, -⟩ := famThree_slice_ranges htS htS1 hg hg1 K1 p1 m
  have hEs := (hr (famPieceSamples (famThreeQr tS gamma q3 m) m rho) (rho / 4)
    (famPieceSamples_pos hrho) h4 h41).2.1
  have hL : 0 < pieceLineExponent Bq2 (famThreeQb tS gS m)
      (famThreeEb (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tS gS m)
      (famThreeEr (familyWidthPrefactor K1) (familyWidthDivisor 1 p1) tS gamma q3 m) rho := by
    unfold pieceLineExponent famThreeEr threeRemE famThreeEb
    positivity
  have hS : 0 < famPieceSliceExponent (famThreeQr tS gamma q3 m) (famThreeEs tS gamma K1 p1 m) m rho := by
    unfold famPieceSliceExponent
    exact hEs
  unfold polyThreeFamExp
  exact section16CappedWidthExponent_pos (by positivity)


/-! ### The extraction step and the large-modulus cover -/

/-- Every sub-relation with a large projection contains a piece. -/
theorem section16_poly_piece_three_of_subrelation
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyThreeThreshold theta gamma ≤ N)
    {Gamma : Finset (Point N 3 × ZMod N)} (hprod : RelationProductProperty gamma Gamma)
    (Delta : Finset (Point N 3 × ZMod N)) (hDelta : Delta ⊆ Gamma)
    (hproj : theta * (N : Real) ^ 3 ≤ (relationProjection Delta).card) :
    Nonempty (PolyPieceThree Delta theta gamma (3 * threeBudget theta gamma)) := by
  classical
  let phi : Point N 3 → ZMod N := fun x =>
    if h : ∃ y, (x, y) ∈ Delta then Classical.choose h else 0
  have hsel : GraphContained (relationProjection Delta) phi Delta := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    have hex : ∃ y, (z.1, y) ∈ Delta := ⟨z.2, by simpa using hz⟩
    simp only [phi, dif_pos hex]
    exact Classical.choose_spec hex
  have hprodB : HasProductProperty (relationProjection Delta) phi gamma :=
    (RelationProductProperty.mono hprod hDelta) _ phi hsel
  have hN3 : (3 : Real) ≤ N := (le_max_left _ _).trans hN
  have hNthr : lemma156ExplicitThreshold 2 (theta / 2) gamma ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNthree : threeThreshold theta gamma ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2
    rw [h2] at hN3
    norm_num at hN3)
  have hβ : theta / 2 * (N : Real) ^ (2 + 1) ≤ (relationProjection Delta).card := by
    have : (0 : Real) ≤ (N : Real) ^ 3 := by positivity
    have h := hproj
    rw [show (2 + 1 : Nat) = 3 from rfl]
    nlinarith
  obtain ⟨B', hB'sub, harr1, harr2⟩ := lemma_15_6_of_density_lower_explicit 2 (theta / 2) gamma
    (by norm_num) (by positivity) (by linarith) hg hg1 N hNthr hprime hodd
    (relationProjection Delta) phi hβ hprodB
  have hθ1 : section16ThetaOne theta gamma 2 = (theta / 2 * gamma / 2) ^ (2 ^ (2 ^ (2 + 5))) := by
    unfold section16ThetaOne
    congr 1
    ring
  have hBarr : section16ThetaOne theta gamma 2 * (N : Real) ^ (17 * 2 + 15) ≤
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
  exact section16_poly_piece_three_data ht ht1 hg hg1 hNthree Delta B' phi hgraph hBarr
    (hprodB.mono hB'sub)

/-- **The large-modulus cover of a three-dimensional relation.** -/
theorem section16_poly_cover_three_large
    {A2 Bq2 : Nat → Real} (hA2 : ∀ q, 0 < A2 q) (hB2 : ∀ q, 0 < Bq2 q)
    (hlemma6 : AbstractFamilyLemma166At 2 (section16PowerWidth A2 Bq2))
    {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hlemma6' : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1)))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyThreeThreshold theta gamma ≤ N)
    (Gamma : Finset (Point N 3 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 3)
    (hprod : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N 3), (1 - theta) * (N : Real) ^ 3 ≤ J.card ∧
      MultiplyLinearWith (polyThreeFamCount K1 p1 theta gamma)
        (polyThreeFamExp A2 Bq2 K1 p1 theta gamma) (restrictRelation Gamma J) := by
  classical
  obtain ⟨hθ₁pos, hθ₁le, hδpos, hδle⟩ := section16_theta_delta_bounds 2 ht ht1 hg hg1
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 2 ht ht1 hg hg1
  have hθ'pos : 0 < threeBudget theta gamma := by unfold threeBudget; positivity
  have hθ'le : threeBudget theta gamma ≤ 1 := by unfold threeBudget; linarith
  set θ' := threeBudget theta gamma with hθ'def
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 2 ht ht1 hg hg1
  let Good : Finset (Point N 3 × ZMod N) → Prop := fun G =>
    ∃ P : PolyPieceThree Gamma theta gamma (3 * θ'), G = partialGraph P.D P.phi
  have hmass : 0 < 3 * θ' * (N : Real) ^ 3 := by
    have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  obtain ⟨q, G, J, hG, hq, hJ, hcov⟩ := section16_greedy_relation_decomposition Good theta
    (3 * θ' * (N : Real) ^ 3) hmass Gamma (by
      intro Delta hDelta hproj
      obtain ⟨P⟩ := section16_poly_piece_three_of_subrelation ht ht1 hg hg1 hN hprod Delta
        hDelta hproj
      refine ⟨partialGraph P.D P.phi, P.graph_sub, ?_, ⟨P.widen hDelta, rfl⟩⟩
      rw [partialGraph_card]
      exact P.card_ge)
  set m := polyThreePieces gamma theta with hmdef
  have hqm : q ≤ m := by
    rw [hmdef, polyThreePieces]
    apply Nat.le_floor
    have hNpos : (0 : Real) < (N : Real) ^ 3 := by
      have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      positivity
    have h1 : (q : Real) * (3 * θ' * (N : Real) ^ 3) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 3 :=
      hq.trans hsize
    rw [le_div_iff₀ (by positivity)]
    have h2 : (q : Real) * (3 * θ') * (N : Real) ^ 3 ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 3 := by
      linarith [h1]
    exact le_of_mul_le_mul_right h2 hNpos
  choose P hPG using fun i => (hG i).2
  let Q : Fin m → PolyPieceThree Gamma theta gamma 0 := fun j =>
    if h : j.val < q then (P ⟨j.val, h⟩).toMassZero
    else PolyPieceThreeData.empty Gamma _ _ _ _ _ _
  have hfam := section16_poly_family_three_cover hA2 hB2 hlemma6 hK1 hp1 hlemma6' hz hzHalf
    hθ'pos hθ'le hδpos hδle hθ'pos hθ'le hg hg1 Q
  refine ⟨J, hJ, MultiplyLinearWith.subset hfam ?_⟩
  intro z hz'
  have hz1 := hcov hz'
  unfold section16FinsetUnion at hz1
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz1
  rw [hPG i] at hi
  refine Finset.mem_biUnion.mpr ⟨⟨i.val, i.isLt.trans_le hqm⟩, Finset.mem_univ _, ?_⟩
  simp only [Q, dif_pos i.isLt]
  exact hi

/-! ### `PolyCoverAt 3` -/

/-- **`PolyCoverAt 3`**, from the family Lemma 16.6 in dimensions one and two. -/
theorem polyCoverAt_three_of_family_lemma6
    {A2 Bq2 : Nat → Real} (hA2 : ∀ q, 0 < A2 q) (hB2 : ∀ q, 0 < Bq2 q)
    (hlemma6 : AbstractFamilyLemma166At 2 (section16PowerWidth A2 Bq2))
    {K1 p1 : Nat} (hK1 : 0 < K1) (hp1 : 0 < p1)
    (hlemma6' : AbstractFamilyLemma166At 1
      (section16PowerWidth (familyWidthPrefactor K1) (familyWidthDivisor 1 p1))) :
    PolyCoverAt 3 (polyThreeQb K1 p1) (polyThreeEb A2 Bq2 K1 p1) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  classical
  by_cases hN : polyThreeThreshold theta gamma ≤ N
  · obtain ⟨J, hJ, hML⟩ := section16_poly_cover_three_large hA2 hB2 hlemma6 hK1 hp1 hlemma6'
      ht ht1 hg hg1 hN Gamma hsize hprod
    refine ⟨J, hJ, MultiplyLinearWith.weaken hML (fun s _ _ => le_max_left _ _) ?_ ?_⟩
    · intro s hs hs1
      exact section16CappedWidthExponent_pos (polyThreeFamExp_pos hB2 hp1 ht ht1 hg hg1 hs hs1)
    · intro s _ _
      exact min_le_left _ _
  · have hNlt : (N : Real) < polyThreeThreshold theta gamma := lt_of_not_ge hN
    refine ⟨Finset.univ, ?_, ?_⟩
    · have hc : ((Finset.univ : Finset (Point N 3)).card : Real) = (N : Real) ^ 3 := by
        simp [Point, ZMod.card]
      rw [hc]
      have : (0 : Real) ≤ (N : Real) ^ 3 := by positivity
      nlinarith
    · exact multiplyLinearWith_of_small_modulus (by norm_num : 0 < 3) hNlt
        (restrictRelation Gamma Finset.univ)
        (polyThreeFamCount K1 p1 theta gamma) (polyThreeFamExp A2 Bq2 K1 p1 theta gamma)
        (fun s hs hs1 => polyThreeFamExp_pos hB2 hp1 ht ht1 hg hg1 hs hs1)
end LeanProofs.GowersSzemeredi
