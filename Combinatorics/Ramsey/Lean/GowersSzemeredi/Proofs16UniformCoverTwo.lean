import GowersSzemeredi.Proofs16PolyCoverTwo

/-! **Uniform family covers in dimension two** (Notes L.3, step (C)).

`PolyCoverAt 2` covers one product relation at a time. Dimension three
needs more: the spectra, remainders and slices of *many* three-dimensional
pieces are two-dimensional relations, and they must be covered on common
cells. This module provides that, in the procedural form of Notes L.3.

* `PolyPieceTwo N θ γ`: the dimension-two pieces of `section16_poly_piece_two_data`,
  with their Freiman data, relative to the universal relation. Pieces of
  different relations are members of one class.
* `section16_poly_piece_decomposition_two`: above Lemma 15.6's threshold,
  every product relation `Γ` of size `≤ γ⁻²N²` has a good set `J` with
  `|J| ≥ (1-θ)N²` and a decomposition of `Γ` over `J` into
  `polyTwoPieces γ θ` pieces of the class. The good set and the pieces
  depend on `Γ` alone.
* `section16_uniform_cover_two`: for any finite family of relations with
  such decompositions, the union of their restrictions is multiply
  multilinear. The controls are those of `section16_poly_family_two_cover`
  at `n·polyTwoPieces γ θ` pieces (`uniTwoCount`, `uniTwoExp`). They are
  polynomial in the family size `n`.

Only the abstract family Lemma 16.6 in dimension one is assumed, as for
`PolyCoverAt 2`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The class of dimension-two pieces at parameters `(θ, γ)`. -/
abbrev PolyPieceTwo (N : Nat) [NeZero N] (theta gamma : Real) :=
  PolyPieceTwoData (Finset.univ : Finset (Point N 2 × ZMod N)) (section16Zeta theta gamma 1) 0
    (polyPieceSpecCount theta gamma) (polyPieceFaceCount theta gamma) (polyPieceFaceCount theta gamma)

/-- The graph of a family of pieces. -/
def polyPieceTwoGraphs {N : Nat} [NeZero N] {theta gamma : Real} {m : Nat}
    (P : Fin m → PolyPieceTwo N theta gamma) : Finset (Point N 2 × ZMod N) :=
  Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi

/-- **Every product relation decomposes into a bounded number of pieces**,
off a good set depending on the relation alone. -/
theorem section16_poly_piece_decomposition_two
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoThreshold theta gamma ≤ N)
    (Gamma : Finset (Point N 2 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2)
    (hprod : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
      ∃ P : Fin (polyTwoPieces gamma theta) → PolyPieceTwo N theta gamma,
        restrictRelation Gamma J ⊆ polyPieceTwoGraphs P := by
  classical
  obtain ⟨hθ₂pos, hθ₂le⟩ := section16ThetaTwo_pos_le 1 ht ht1 hg hg1
  have hθ'pos : 0 < polyPieceBudget theta gamma := by
    unfold polyPieceBudget; positivity
  set θ' := polyPieceBudget theta gamma with hθ'def
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
  let Q : Fin m → PolyPieceTwo N theta gamma := fun j =>
    if h : j.val < q then ((P ⟨j.val, h⟩).toMassZero).widen (Finset.subset_univ _)
    else PolyPieceTwoData.empty _ zeta qs qf qf
  refine ⟨J, hJ, Q, ?_⟩
  intro z hz'
  have hz1 := hcov hz'
  unfold section16FinsetUnion at hz1
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz1
  rw [hPG i] at hi
  refine Finset.mem_biUnion.mpr ⟨⟨i.val, i.isLt.trans_le hqm⟩, Finset.mem_univ _, ?_⟩
  simp only [Q, dif_pos i.isLt]
  exact hi

/-! ### The uniform family cover -/

/-- The count control of the uniform cover at `M` pieces. -/
def uniTwoCount (theta gamma : Real) (M : Nat) : Real → Real :=
  fun rho => max (famPieceGraphBound (famTwoQr M (polyPieceFaceCount theta gamma))
      (famTwoPb M (polyPieceFaceCount theta gamma)) M rho)
    ((3 ^ (1 + 1) * M : Nat) : Real)

/-- The width-exponent control of the uniform cover at `M` pieces. -/
def uniTwoExp (A Bq : Nat → Real) (theta gamma : Real) (M : Nat) : Real → Real :=
  fun rho =>
    let qs := polyPieceSpecCount theta gamma
    let qf := polyPieceFaceCount theta gamma
    section16CappedWidthExponent
      (pieceLineExponent Bq (famTwoQb M qs) (famTwoEb M qs) (famTwoEr M qf) rho *
        famPieceSliceExponent (famTwoQr M qf) (famTwoEs M qf) M rho / 4)
      (section16RoundedPowerThreshold (pieceWidthScale A (famTwoQb M qs) (section16Zeta theta gamma 1) rho)
        (pieceLineExponent Bq (famTwoQb M qs) (famTwoEb M qs) (famTwoEr M qf) rho)
        (famPieceSliceExponent (famTwoQr M qf) (famTwoEs M qf) M rho))

/-- Any finite family of pieces of the class is covered simultaneously. -/
theorem section16_poly_piece_two_family_cover {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {M : Nat} (P : Fin M → PolyPieceTwo N theta gamma) :
    MultiplyLinearWith (uniTwoCount theta gamma M) (uniTwoExp A Bq theta gamma M)
      (polyPieceTwoGraphs P) := by
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half 1 ht ht1 hg hg1
  exact section16_poly_family_two_cover hA hB hlemma6 hz hzHalf P

/-- **The uniform family cover in dimension two.** A family of `n` relations,
each decomposed into `m` pieces of the class, has one cover of the union of
their restrictions, with the controls at `n·m` pieces. -/
theorem section16_uniform_cover_two {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n m : Nat}
    (Gammas : Fin n → Finset (Point N 2 × ZMod N)) (J : Fin n → Finset (Point N 2))
    (P : Fin n → Fin m → PolyPieceTwo N theta gamma)
    (hcov : ∀ i, restrictRelation (Gammas i) (J i) ⊆ polyPieceTwoGraphs (P i)) :
    MultiplyLinearWith (uniTwoCount theta gamma (n * m)) (uniTwoExp A Bq theta gamma (n * m))
      (Finset.univ.biUnion fun i => restrictRelation (Gammas i) (J i)) := by
  classical
  let e : Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
  let R : Fin (n * m) → PolyPieceTwo N theta gamma := fun c => P (e c).1 (e c).2
  refine MultiplyLinearWith.subset
    (section16_poly_piece_two_family_cover hA hB hlemma6 ht ht1 hg hg1 R) ?_
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hcov i hi)
  refine Finset.mem_biUnion.mpr ⟨e.symm (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.apply_symm_apply]
  exact hc

end LeanProofs.GowersSzemeredi
