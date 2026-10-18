import GowersSzemeredi.Proofs16PolyFamilyTwo
import GowersSzemeredi.Proofs16GreedyRelations

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
(`exists_abstract_family_lemma_16_6`).

`polyCoverAt_two_of_family_lemma6`, `polyTwoEb`, `polyTwoQb`,
`polyTwoThreshold`, `section16_poly_cover_two_large` and
`section16_poly_piece_two_of_subrelation` are in `Proofs16PolyCoverTwoSide`,
outside the final route. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- A relation has at most one modulus worth of values over any point. -/
theorem relation_fiber_card_le_modulus {N k : Nat} [NeZero N]
    (Gamma : Finset (Point N k × ZMod N)) (x : Point N k) :
    (Gamma.filter fun z => z.1 = x).card ≤ N := by
  refine (Finset.card_le_card_of_injOn (fun z => z.2) (fun _ _ => Finset.mem_univ _)
    ?_).trans (by simp [ZMod.card])
  intro z hz z' hz' h
  exact Prod.ext ((Finset.mem_filter.mp hz).2.trans (Finset.mem_filter.mp hz').2.symm) h

/-- Below the threshold, every box is covered by the coarse relation construction. -/
theorem multiplyLinearWith_of_small_modulus {N k : Nat} [NeZero N]
    (hk : 0 < k) {T : Real} (hN : (N : Real) < T)
    (Gamma : Finset (Point N k × ZMod N)) (Q E : Real → Real)
    (hE : ∀ s, 0 < s → s ≤ 1 → 0 < E s) :
    MultiplyLinearWith
      (fun s => max (Q s) ((3 ^ k * ⌈T⌉₊ : Nat) : Real))
      (fun s => section16CappedWidthExponent (E s) T) Gamma := by
  refine multiplyLinearWith_of_large_box_covers hk ⌈T⌉₊ ?_ Q E (fun _ => T) hE ?_
  · intro x
    refine (relation_fiber_card_le_modulus Gamma x).trans ?_
    exact_mod_cast hN.le.trans (Nat.le_ceil T)
  · intro s _ _ P hP hlarge
    exfalso
    have hw : (P.width : Real) ≤ N := by exact_mod_cast P.width_le_modulus hP
    linarith

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

/-- Extract and pad a dimension-two family with the exact floor of the mass ratio. -/
theorem section16_poly_piece_two_decomposition_of_extract
    {N : Nat} [NeZero N] {theta mass cap zeta : Real} {qs qr ql : Nat}
    (hmass : 0 < mass) (Gamma : Finset (Point N 2 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ cap * (N : Real) ^ 2)
    (hextract : ∀ Delta ⊆ Gamma,
      theta * (N : Real) ^ 2 ≤ (relationProjection Delta).card →
      Nonempty (PolyPieceTwoData Delta zeta mass qs qr ql)) :
    ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
      ∃ P : Fin ⌊cap / mass⌋₊ →
        PolyPieceTwoData (Finset.univ : Finset (Point N 2 × ZMod N)) zeta 0 qs qr ql,
        restrictRelation Gamma J ⊆ Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi := by
  have hNpos : 0 < (N : Real) ^ 2 := by
    have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  let Good : Finset (Point N 2 × ZMod N) → Prop := fun G =>
    ∃ P : PolyPieceTwoData Finset.univ zeta mass qs qr ql, G = partialGraph P.D P.phi
  obtain ⟨q, G, J, hG, hq, hJ, hcov⟩ := section16_greedy_relation_decomposition Good theta
    (mass * (N : Real) ^ 2) (mul_pos hmass hNpos) Gamma (by
      intro Delta hDelta hproj
      obtain ⟨P⟩ := hextract Delta hDelta hproj
      refine ⟨partialGraph P.D P.phi, P.graph_sub, ?_, ⟨P.widen (Finset.subset_univ _), rfl⟩⟩
      rw [partialGraph_card]
      exact P.card_ge)
  have hqm : q ≤ ⌊cap / mass⌋₊ := by
    apply Nat.le_floor
    rw [le_div_iff₀ hmass]
    apply le_of_mul_le_mul_right (a := (N : Real) ^ 2) _ hNpos
    simpa only [mul_assoc] using hq.trans hsize
  choose P hPG using fun i => (hG i).2
  let Q : Fin ⌊cap / mass⌋₊ → PolyPieceTwoData Finset.univ zeta 0 qs qr ql := fun j =>
    if h : j.val < q then (P ⟨j.val, h⟩).toMassZero else PolyPieceTwoData.empty _ zeta qs qr ql
  refine ⟨J, hJ, Q, ?_⟩
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hcov hz)
  rw [hPG i] at hi
  refine Finset.mem_biUnion.mpr ⟨⟨i.val, i.isLt.trans_le hqm⟩, Finset.mem_univ _, ?_⟩
  simp only [Q, dif_pos i.isLt]
  exact hi

/-! ### Parameters -/

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

/-! ### `PolyCoverAt 2` -/

theorem polyTwoFamExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} {rho : Real} (hrho : 0 < rho) :
    0 < polyTwoFamExp A Bq theta gamma rho := by
  unfold polyTwoFamExp
  exact famTwoCappedExponent_pos hB hrho

end LeanProofs.GowersSzemeredi
