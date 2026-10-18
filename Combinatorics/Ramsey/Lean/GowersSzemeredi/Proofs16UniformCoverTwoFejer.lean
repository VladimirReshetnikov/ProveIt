import GowersSzemeredi.Proofs18FejerSeedExponents
import GowersSzemeredi.Proofs16SplitUniformClass

/-! **The dimension-two uniform class under the Fejér θ₁ and the tight
radius: the split-class seed** (Notes L.16d).

The Fejér analogues of `Proofs16UniformCoverTwo`,
`Proofs16UniformCoverTwoBounds` and the dimension-two part of
`Proofs16PowerUniformClass`, generated from them by a script with a guard
that no printed quantity survives:
* `PolyPieceTwoFejer N θ γ`: the dimension-two pieces at the tight radius
  with the Fejér counts;
* `section16_poly_piece_decomposition_two_fejer` and
  `section16_uniform_cover_two_fejer`;
* `uniTwoFejerCount_le_power` (`≤ w^(2^43)`, printed `2^89`) and
  `uniTwoFejerExp_inv_le_power` (`≤ w^(2^46)`, printed `2^130`);
* `powerUniformClass_two_fejer : PowerUniformClass 2 V (2^43) (2^46) (2^15)`
  (printed `(2^89, 2^130, 2^45)`);
* `splitUniformClass_two_fejer`: a split class at `a = D = 2^46`, the seed
  of the split-class recursion. This is inside the `2^48` of
  `split_pair_with_bounds_fourteen`, against the printed `2^132`.

`powerUniformClass_two_fejer`, `splitUniformClass_two_fejer` and
`uniTwoFejerExp_inv_le_power` are in `Proofs16UniformCoverTwoFejerSide`, outside
the final route. -/
set_option autoImplicit false
set_option exponentiation.threshold 1024
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- The class of dimension-two pieces at parameters `(θ, γ)`. -/
abbrev PolyPieceTwoFejer (N : Nat) [NeZero N] (theta gamma : Real) :=
  PolyPieceTwoData (Finset.univ : Finset (Point N 2 × ZMod N)) (tightZeta (fejerThetaOne theta gamma 1 / 4)) 0
    (polyPieceSpecCountW (fejerThetaOne theta gamma 1)) (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma) (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma)

/-- The graph of a family of pieces. -/
def polyPieceTwoFejerGraphs {N : Nat} [NeZero N] {theta gamma : Real} {m : Nat}
    (P : Fin m → PolyPieceTwoFejer N theta gamma) : Finset (Point N 2 × ZMod N) :=
  Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi

/-- **Every product relation decomposes into a bounded number of pieces**,
off a good set depending on the relation alone. -/
theorem section16_poly_piece_decomposition_two_fejer
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : polyTwoFejerThreshold theta gamma ≤ N)
    (Gamma : Finset (Point N 2 × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ 2)
    (hprod : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N 2), (1 - theta) * (N : Real) ^ 2 ≤ J.card ∧
      ∃ P : Fin (polyTwoFejerPieces gamma theta) → PolyPieceTwoFejer N theta gamma,
        restrictRelation Gamma J ⊆ polyPieceTwoFejerGraphs P := by
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hθ₂pos, _⟩ := section16ThetaTwo_pos_le_with hfa0 hfaS
  have hmass : 0 < 5 * polyPieceBudgetW (fejerThetaOne theta gamma 1) := by
    unfold polyPieceBudgetW; positivity
  exact section16_poly_piece_two_decomposition_of_extract hmass Gamma hsize
    (fun Delta hDelta hproj =>
      section16_poly_piece_two_of_subrelation_fejer ht ht1 hg hg1 hN hprod Delta hDelta hproj)

/-! ### The uniform family cover -/

/-- The count control of the uniform cover at `M` pieces. -/
def uniTwoFejerCount (theta gamma : Real) (M : Nat) : Real → Real :=
  fun rho => max (famPieceGraphBound (famTwoQr M (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma))
      (famTwoPb M (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma)) M rho)
    ((3 ^ (1 + 1) * M : Nat) : Real)

/-- The width-exponent control of the uniform cover at `M` pieces. -/
def uniTwoFejerExp (A Bq : Nat → Real) (theta gamma : Real) (M : Nat) : Real → Real :=
  fun rho =>
    let qs := polyPieceSpecCountW (fejerThetaOne theta gamma 1)
    let qf := polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma
    section16CappedWidthExponent
      (pieceLineExponent Bq (famTwoQb M qs) (famTwoEb M qs) (famTwoEr M qf) rho *
        famPieceSliceExponent (famTwoQr M qf) (famTwoEs M qf) M rho / 4)
      (section16RoundedPowerThreshold (pieceWidthScale A (famTwoQb M qs) (tightZeta (fejerThetaOne theta gamma 1 / 4)) rho)
        (pieceLineExponent Bq (famTwoQb M qs) (famTwoEb M qs) (famTwoEr M qf) rho)
        (famPieceSliceExponent (famTwoQr M qf) (famTwoEs M qf) M rho))

/-- Any finite family of pieces of the class is covered simultaneously. -/
theorem section16_poly_piece_two_family_cover_fejer {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {M : Nat} (P : Fin M → PolyPieceTwoFejer N theta gamma) :
    MultiplyLinearWith (uniTwoFejerCount theta gamma M) (uniTwoFejerExp A Bq theta gamma M)
      (polyPieceTwoFejerGraphs P) := by
  obtain ⟨hfa0, hfaS⟩ := fejerThetaOne_one_bounds ht ht1 hg hg1
  obtain ⟨hz, hzHalf⟩ := tightZeta_pos_le_half hfa0 (by linarith)
  exact section16_poly_family_two_cover hA hB hlemma6 hz hzHalf P

/-- **The uniform family cover in dimension two.** A family of `n` relations,
each decomposed into `m` pieces of the class, has one cover of the union of
their restrictions, with the controls at `n·m` pieces. -/
theorem section16_uniform_cover_two_fejer {A Bq : Nat → Real} (hA : ∀ q, 0 < A q)
    (hB : ∀ q, 0 < Bq q) (hlemma6 : AbstractFamilyLemma166At 1 (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n m : Nat}
    (Gammas : Fin n → Finset (Point N 2 × ZMod N)) (J : Fin n → Finset (Point N 2))
    (P : Fin n → Fin m → PolyPieceTwoFejer N theta gamma)
    (hcov : ∀ i, restrictRelation (Gammas i) (J i) ⊆ polyPieceTwoFejerGraphs (P i)) :
    MultiplyLinearWith (uniTwoFejerCount theta gamma (n * m)) (uniTwoFejerExp A Bq theta gamma (n * m))
      (Finset.univ.biUnion fun i => restrictRelation (Gammas i) (J i)) := by
  let e : Fin (n * m) ≃ Fin n × Fin m := finProdFinEquiv.symm
  let R : Fin (n * m) → PolyPieceTwoFejer N theta gamma := fun c => P (e c).1 (e c).2
  refine MultiplyLinearWith.subset
    (section16_poly_piece_two_family_cover_fejer hA hB hlemma6 ht ht1 hg hg1 R) ?_
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hcov i hi)
  refine Finset.mem_biUnion.mpr ⟨e.symm (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.apply_symm_apply]
  exact hc

theorem uniTwoFejerExp_pos {A Bq : Nat → Real} (hB : ∀ q, 0 < Bq q)
    {theta gamma : Real} (M : Nat) {rho : Real} (hrho : 0 < rho) :
    0 < uniTwoFejerExp A Bq theta gamma M rho := by
  unfold uniTwoFejerExp
  exact famTwoCappedExponent_pos hB hrho

theorem uniTwoFejerCount_le_power {gamma theta rho : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hr : 0 < rho) (hr1 : rho ≤ 1)
    {w : Real} (hvw : 2 / (gamma * theta) ≤ w) (hrw : rho⁻¹ ≤ w)
    {M : Nat} (hM : (M : Real) ≤ w ^ ((2 : Nat) ^ 38)) :
    uniTwoFejerCount theta gamma M rho ≤ w ^ ((2 : Nat) ^ 43) := by
  obtain ⟨hv2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hq := polyPieceFaceCountW_fejer_le_power hg hg1 ht ht1
  set v := 2 / (gamma * theta) with hv
  clear_value v
  have hw2 : 2 ≤ w := hv2.trans hvw
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv2
  -- both counts below `w^(2^38)`
  have hq' : (polyPieceFaceCountW (fejerThetaOne theta gamma 1) gamma : Real) ≤ w ^ ((2 : Nat) ^ 38) :=
    hq.trans (pow_le_pow_left₀ hv0 hvw _)
  unfold uniTwoFejerCount
  exact le_pow_mono hw2 (by norm_num) (famTwoCount_le_power hw2 hr hrw hM hq')

theorem nPieces_le_base_fejer {gamma theta : Real} (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta)
    (ht1 : theta ≤ 1) {n : Nat} {w : Real} (hvw : 2 / (gamma * theta) ≤ w)
    (hnw : (n : Real) + 1 ≤ w) (hw2 : 2 ≤ w) :
    ((n * polyTwoFejerPieces gamma theta : Nat) : Real) ≤ w ^ ((2 : Nat) ^ 38) := by
  have hm := polyTwoFejerPieces_le_power hg hg1 ht ht1
  obtain ⟨hu2, -, -, -, -⟩ := prod_scale_basic hg hg1 ht ht1
  have hw1 : 1 ≤ w := by linarith only [hw2]
  have hmw : (polyTwoFejerPieces gamma theta : Real) ≤ w ^ ((2 : Nat) ^ 24) :=
    hm.trans (pow_le_pow_left₀ (by linarith only [hu2]) hvw _)
  have hn : (n : Real) ≤ w := by linarith only [hnw]
  calc ((n * polyTwoFejerPieces gamma theta : Nat) : Real)
      = (n : Real) * (polyTwoFejerPieces gamma theta : Real) := by push_cast; ring
    _ ≤ w * w ^ ((2 : Nat) ^ 24) :=
        mul_le_mul hn hmw (Nat.cast_nonneg _) (by linarith only [hw2])
    _ = w ^ ((2 : Nat) ^ 24 + 1) := by rw [pow_succ]; ring
    _ ≤ w ^ ((2 : Nat) ^ 38) := pow_le_pow_right₀ hw1 (by norm_num)

end LeanProofs.GowersSzemeredi
