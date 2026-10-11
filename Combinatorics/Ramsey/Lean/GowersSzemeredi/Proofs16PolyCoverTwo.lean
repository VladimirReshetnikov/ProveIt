import GowersSzemeredi.Proofs16PolyFamilyTwo
import GowersSzemeredi.Proofs16GreedyRelations
import GowersSzemeredi.Proofs15ExplicitThresholds

/-! **`PolyCoverAt 2` from the abstract family Lemma 16.6.**

The open core of Notes L.3: a polynomial global-to-local cover of every
two-dimensional relation with the product property. It is assembled from
* the peeling loop `section16_greedy_relation_decomposition`. Each
  sub-relation with projection at least `θN²` yields a piece: a
  one-value-per-point selection inherits the product property
  (`RelationProductProperty`), Lemma 15.6
  (`lemma_15_6_of_density_lower_explicit`, `β = θ/2`) gives Lemma 16.4's
  arrangement conditions, and `section16_poly_piece_two_data` gives the
  piece with its Freiman data;
* padding with empty pieces to the deterministic number
  `polyTwoPieces γ θ = ⌊γ⁻²/(5θ′)⌋`, so that the controls depend only on
  `(γ, θ, ρ)`;
* the simultaneous cover `section16_poly_family_two_cover`;
* below Lemma 15.6's threshold `polyTwoThreshold θ γ` (polynomial in
  `1/θγ`), the coarse relation cover through
  `multiplyLinearWith_of_large_box_covers`, whose large-box premise is then
  vacuous.

The only input is `AbstractFamilyLemma166At 1` at the polynomial power
width. The heavy bridge supplies it from the polynomial recurrence
(`exists_abstract_family_lemma_16_6`). -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-! ### Operations on piece data -/

theorem relFreimanCover_empty {N : Nat} [NeZero N] (q : Nat) :
    RelFreimanCover q (∅ : Finset (Point N 1 × ZMod N)) := by
  refine ⟨fun _ => ∅, fun _ => 0, fun _ => ?_, Finset.empty_subset _⟩
  show IsAddFreimanHom 8 _ Set.univ (fun _ => (0 : ZMod N))
  exact isAddFreimanHom_const (Set.mem_univ _)

/-- A piece of a sub-relation is a piece of the relation. -/
def PolyPieceTwoData.widen {N : Nat} [NeZero N] {Gamma Gamma' : Finset (Point N 2 × ZMod N)}
    {zeta mass : Real} {qs qr ql : Nat} (P : PolyPieceTwoData Gamma' zeta mass qs qr ql)
    (hsub : Gamma' ⊆ Gamma) : PolyPieceTwoData Gamma zeta mass qs qr ql :=
  { P with graph_sub := P.graph_sub.trans hsub }

/-- Forget the mass bound. -/
def PolyPieceTwoData.toMassZero {N : Nat} [NeZero N] {Gamma : Finset (Point N 2 × ZMod N)}
    {zeta mass : Real} {qs qr ql : Nat} (P : PolyPieceTwoData Gamma zeta mass qs qr ql) :
    PolyPieceTwoData Gamma zeta 0 qs qr ql :=
  { P with card_ge := by simp }

/-- The empty piece. -/
def PolyPieceTwoData.empty {N : Nat} [NeZero N] (Gamma : Finset (Point N 2 × ZMod N))
    (zeta : Real) (qs qr ql : Nat) : PolyPieceTwoData Gamma zeta 0 qs qr ql where
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
  spec := (relFreimanCover_empty qs).mono (by intro z hz; simp at hz)
  remc := (relFreimanCover_empty qr).mono (by intro z hz; simp at hz)
  slices := by
    intro t
    refine ⟨fun _ => ∅, fun _ => 0, fun _ => ?_, ?_⟩
    · show IsAddFreimanHom 8 _ Set.univ (fun _ => (0 : ZMod N))
      exact isAddFreimanHom_const (Set.mem_univ _)
    · intro z hz
      obtain ⟨x, hx, -⟩ := Finset.mem_image.mp hz
      simp [section16FinalCoordinateSection] at hx

/-! ### Parameters -/

/-- Lemma 15.6's modulus threshold at `β = θ/2`, and at least `3`. -/
def polyTwoThreshold (theta gamma : Real) : Real :=
  max 3 (lemma156ExplicitThreshold 1 (theta / 2) gamma)

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

theorem two_rpow_neg_44 : (2 : Real) ^ (-(44 : Real)) = (2 : Real)⁻¹ ^ 44 := by
  rw [show (-(44 : Real)) = ((-44 : Int) : Real) by norm_num, Real.rpow_intCast,
    zpow_neg, inv_pow]
  norm_num

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
    have h := hproj
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
  classical
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
  set θ' := polyPieceBudget theta gamma with hθ'def
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  set zeta := section16Zeta theta gamma 1 with hzetadef
  set qs := polyPieceSpecCount theta gamma
  set qf := polyPieceFaceCount theta gamma
  let Good : Finset (Point N 2 × ZMod N) → Prop := fun G =>
    ∃ P : PolyPieceTwoData Gamma zeta (5 * θ') qs qf qf, G = partialGraph P.D P.phi
  have hmass : 0 < 5 * θ' * (N : Real) ^ 2 := by
    have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  obtain ⟨q, G, J, hG, hq, hJ, hcov⟩ := section16_greedy_relation_decomposition Good theta
    (5 * θ' * (N : Real) ^ 2) hmass Gamma (by
      intro Delta hDelta hproj
      obtain ⟨P⟩ := section16_poly_piece_two_of_subrelation ht ht1 hg hg1 hN hprod Delta
        hDelta hproj
      refine ⟨partialGraph P.D P.phi, P.graph_sub, ?_, ⟨P.widen hDelta, rfl⟩⟩
      rw [partialGraph_card]
      exact P.card_ge)
  -- the number of pieces
  set m := polyTwoPieces gamma theta with hmdef
  have hqm : q ≤ m := by
    rw [hmdef, polyTwoPieces]
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
def polyTwoQb (gamma theta : Real) : Real → Real :=
  fun rho => max (polyTwoFamCount theta gamma rho)
    ((3 ^ 2 * ⌈polyTwoThreshold theta gamma⌉₊ : Nat) : Real)

/-- The width-exponent control of `PolyCoverAt 2`. -/
def polyTwoEb (A Bq : Nat → Real) (gamma theta : Real) : Real → Real :=
  fun rho => section16CappedWidthExponent (polyTwoFamExp A Bq theta gamma rho)
    (polyTwoThreshold theta gamma)

theorem polyTwoFamExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} {rho : Real} (hrho : 0 < rho) :
    0 < polyTwoFamExp A Bq theta gamma rho := by
  unfold polyTwoFamExp
  apply section16CappedWidthExponent_pos
  have h8 : 0 < rho / 8 := by positivity
  have h4 : 0 < rho / 4 := by positivity
  have hEb := cubicBaseExponent_pos
    (Nat.succ_pos (polyTwoPieces gamma theta * polyPieceSpecCount theta gamma)) h8
  have hEr := cubicBaseExponent_pos
    (Nat.succ_pos (polyTwoPieces gamma theta * polyPieceFaceCount theta gamma)) h8
  have hEs := cubicBaseExponent_pos (Nat.succ_pos (polyTwoPieces gamma theta *
    (famPieceSamples (famTwoQr (polyTwoPieces gamma theta) (polyPieceFaceCount theta gamma))
      (polyTwoPieces gamma theta) rho * polyPieceFaceCount theta gamma))) h4
  have hBq := hB ⌊famTwoQb (polyTwoPieces gamma theta) (polyPieceSpecCount theta gamma)
    (rho / 8)⌋₊
  simp only [pieceLineExponent, famPieceSliceExponent, famTwoEb, famTwoEr, famTwoEs]
  positivity

/-- **`PolyCoverAt 2`**, from the family Lemma 16.6 at a power width. -/
theorem polyCoverAt_two_of_family_lemma6 {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq)) :
    PolyCoverAt 2 polyTwoQb (polyTwoEb A Bq) := by
  intro N _ _ gamma theta hg hg1 ht ht1 Gamma hsize hprod
  classical
  by_cases hN : polyTwoThreshold theta gamma ≤ N
  · obtain ⟨J, hJ, hML⟩ := section16_poly_cover_two_large hA hB hlemma6 ht ht1 hg hg1 hN
      Gamma hsize hprod
    refine ⟨J, hJ, MultiplyLinearWith.weaken hML (fun s _ _ => le_max_left _ _) ?_ ?_⟩
    · intro s hs hs1
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
    · have hfib : ∀ x : Point N 2,
          ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤
            ⌈polyTwoThreshold theta gamma⌉₊ := by
        intro x
        have h1 : ((restrictRelation Gamma Finset.univ).filter fun z => z.1 = x).card ≤ N := by
          refine (Finset.card_le_card_of_injOn (fun z => z.2) (fun _ _ => Finset.mem_univ _)
            ?_).trans (by simp [ZMod.card])
          intro z hz z' hz' h
          exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) h
        refine h1.trans ?_
        have : (N : Real) ≤ ⌈polyTwoThreshold theta gamma⌉₊ :=
          hNlt.le.trans (Nat.le_ceil _)
        exact_mod_cast this
      have hcov := multiplyLinearWith_of_large_box_covers (by norm_num : 0 < 2)
        (Gamma := restrictRelation Gamma Finset.univ) ⌈polyTwoThreshold theta gamma⌉₊ hfib
        (polyTwoFamCount theta gamma) (polyTwoFamExp A Bq theta gamma)
        (fun _ => polyTwoThreshold theta gamma)
        (fun s hs hs1 => polyTwoFamExp_pos hB hs) (by
          intro s _ _ P hP hlarge
          exfalso
          have hw : (P.width : Real) ≤ N := by exact_mod_cast P.width_le_modulus hP
          linarith)
      exact hcov

end LeanProofs.GowersSzemeredi
