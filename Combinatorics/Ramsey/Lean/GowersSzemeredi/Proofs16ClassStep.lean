import GowersSzemeredi.Proofs16ClassPieceCover

/-! The step of route (II): pieces of `(k+1)`-dimensional relations
(Notes L.6, E4).

Let `C` be a uniform class of dimension `k ≥ 1`.
* `class_piece_of_subrelation`: above `classStepThreshold`, every
  sub-relation `Δ ⊆ Γ` of a product relation with projection of size
  `≥ θN^(k+1)` contains a `ClassPiece` of mass `θ′`. The input is Lemma 15.6
  at dimension `k` with `β = θ/2`, whose arrangement parameter is exactly
  `section16ThetaOne θ γ k`.
* `class_step_decomp`: the greedy decomposition. Off a good set `J` with
  `|J| ≥ (1-θ)N^(k+1)`, the restriction of `Γ` is covered by
  `classPieces γ θ k = ⌊γ⁻²/θ′⌋` pieces of the universal class `StepPiece`.
* `class_step_cover`: any `n` relations so covered have one cover, the
  family cover of their `n·classPieces γ θ k` pieces
  (`class_piece_family_cover`).

So the relations covered by `classPieces γ θ k` step pieces form the next
uniform class, with the raw controls of the family cover. E5 bounds those
controls by powers. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

variable {k : Nat} {Thr : Real → Real → Real} {Cnt Exp : Real → Real → Nat → Real → Real}

/-! ### Operations on pieces -/

/-- A piece of a sub-relation is a piece of the relation. -/
def ClassPiece.widen (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N]
    {Gamma Gamma' : Finset (Point N (k + 1) × ZMod N)} {zeta mass thS gS thF gF : Real}
    (P : ClassPiece C Gamma' zeta mass thS gS thF gF) (hsub : Gamma' ⊆ Gamma) :
    ClassPiece C Gamma zeta mass thS gS thF gF :=
  { P with graph_sub := P.graph_sub.trans hsub }

/-- Forget the mass bound. -/
def ClassPiece.toMassZero (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N]
    {Gamma : Finset (Point N (k + 1) × ZMod N)} {zeta mass thS gS thF gF : Real}
    (P : ClassPiece C Gamma zeta mass thS gS thF gF) :
    ClassPiece C Gamma zeta 0 thS gS thF gF :=
  { P with card_ge := by simp }

/-- The empty piece. -/
def ClassPiece.empty (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N]
    (Gamma : Finset (Point N (k + 1) × ZMod N)) (zeta thS gS thF gF : Real) :
    ClassPiece C Gamma zeta 0 thS gS thF gF where
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
  linear := by intro x hx; simp at hx
  dom := by intro z hz; simp at hz
  G := fun _ _ => 0
  ident := by intro z hz; simp at hz
  spec_U := by
    have h : pieceSpecRel (∅ : Finset (Point N k)) (fun _ => ∅) = ∅ := by
      ext z; simp [pieceSpecRel]
    rw [h]; exact C.empty N thS gS
  face_U := by
    intro e _
    have h : pieceFaceRel (∅ : Finset (Point N (k + 1))) (fun _ _ => (0 : ZMod N)) e = ∅ := by
      ext z; simp [pieceFaceRel]
    rw [h]; exact C.empty N thF gF
  slice_U := by
    intro t
    have h : partialGraph (section16FinalCoordinateSection (∅ : Finset (Point N (k + 1))) t)
        (section16FinalCoordinateRestriction (0 : Point N (k + 1) → ZMod N) t) = ∅ := by
      ext z; simp [partialGraph, section16FinalCoordinateSection]
    rw [h]; exact C.empty N thF gF

/-! ### Parameters of the step -/

/-- Pieces per relation: `⌊γ⁻²/θ′⌋`. -/
def classPieces (gamma theta : Real) (k : Nat) : Nat :=
  ⌊gamma ^ (-(2 : Int)) / classBudget theta gamma k⌋₊

/-- The modulus threshold of the step. -/
def classStepThr (Thr : Real → Real → Real) (theta gamma : Real) (k : Nat) : Real :=
  max 3 (max (lemma156ExplicitThreshold k (theta / 2) gamma) (classPieceThr Thr theta gamma k))

/-- The modulus threshold of the step, for power controls. -/
def classStepThreshold (V : Real) (dT : Nat) (theta gamma : Real) (k : Nat) : Real :=
  max 3 (max (lemma156ExplicitThreshold k (theta / 2) gamma) (classPieceThreshold V dT theta gamma k))

theorem classStepThreshold_eq (V : Real) (dT : Nat) (theta gamma : Real) (k : Nat) :
    classStepThreshold V dT theta gamma k =
      classStepThr (fun theta gamma => (V * (2 / (gamma * theta))) ^ dT) theta gamma k := rfl

/-- The pieces of the next class: relative to the universal relation, mass `0`. -/
abbrev StepPiece (C : UniformClassWith k Thr Cnt Exp) (N : Nat) [NeZero N] (theta gamma : Real) :=
  ClassPiece C (Finset.univ : Finset (Point N (k + 1) × ZMod N)) (section16Zeta theta gamma k) 0
    (classBudget theta gamma k) (classDelta theta gamma k) (classBudget theta gamma k) gamma

/-- The graph of a family of step pieces. -/
def stepPieceGraphs (C : UniformClassWith k Thr Cnt Exp) {N : Nat} [NeZero N] {theta gamma : Real}
    {m : Nat} (P : Fin m → StepPiece C N theta gamma) : Finset (Point N (k + 1) × ZMod N) :=
  Finset.univ.biUnion fun c => partialGraph (P c).D (P c).phi

/-! ### One piece of a sub-relation -/

theorem thetaOne_half_eq (theta gamma : Real) (k : Nat) :
    section16ThetaOne theta gamma k = (theta / 2 * gamma / 2) ^ (2 ^ (2 ^ (k + 5))) := by
  unfold section16ThetaOne
  congr 1
  ring

/-- **Every dense sub-relation contains a piece.** -/
theorem class_piece_of_subrelation (C : UniformClassWith k Thr Cnt Exp) (hk : 1 ≤ k)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : classStepThr Thr theta gamma k ≤ N)
    {Gamma : Finset (Point N (k + 1) × ZMod N)} (hprod : RelationProductProperty gamma Gamma)
    (Delta : Finset (Point N (k + 1) × ZMod N)) (hDelta : Delta ⊆ Gamma)
    (hproj : theta * (N : Real) ^ (k + 1) ≤ (relationProjection Delta).card) :
    Nonempty (ClassPiece C Delta (section16Zeta theta gamma k) (classBudget theta gamma k)
      (classBudget theta gamma k) (classDelta theta gamma k) (classBudget theta gamma k) gamma) := by
  let phi : Point N (k + 1) → ZMod N := fun x =>
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
  have hNthr : lemma156ExplicitThreshold k (theta / 2) gamma ≤ N :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNpiece : classPieceThr Thr theta gamma k ≤ N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hprime : N.Prime := Fact.out
  have hodd : Odd N := hprime.odd_of_ne_two (by
    intro h2
    rw [h2] at hN3
    norm_num at hN3)
  have hβ : theta / 2 * (N : Real) ^ (k + 1) ≤ (relationProjection Delta).card := by
    have : (0 : Real) ≤ (N : Real) ^ (k + 1) := by positivity
    nlinarith
  obtain ⟨B', hB'sub, harr1, harr2⟩ := lemma_15_6_of_density_lower_explicit k (theta / 2) gamma
    hk (by positivity) (by linarith) hg hg1 N hNthr hprime hodd
    (relationProjection Delta) phi hβ hprodB
  have hBarr : section16ThetaOne theta gamma k * (N : Real) ^ (17 * k + 15) ≤
        generalArrangementCount 8 B' ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B' ≤
        respectedGeneralArrangementCount 8 B' phi := by
    refine ⟨?_, ?_⟩
    · rw [thetaOne_half_eq]; exact harr1
    · rw [two_rpow_neg_44]; exact harr2
  have hgraph : partialGraph B' phi ⊆ Delta := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact hsel x (hB'sub hx)
  exact class_piece_data C ht ht1 hg hg1 hNpiece Delta B' phi hgraph hBarr (hprodB.mono hB'sub)

/-! ### The greedy decomposition -/

/-- **Off a good set, a product relation is covered by `classPieces γ θ k` pieces.** -/
theorem class_step_decomp (C : UniformClassWith k Thr Cnt Exp) (hk : 1 ≤ k)
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (hN : classStepThr Thr theta gamma k ≤ N)
    (Gamma : Finset (Point N (k + 1) × ZMod N))
    (hsize : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1))
    (hprod : RelationProductProperty gamma Gamma) :
    ∃ J : Finset (Point N (k + 1)), (1 - theta) * (N : Real) ^ (k + 1) ≤ J.card ∧
      ∃ P : Fin (classPieces gamma theta k) → StepPiece C N theta gamma,
        restrictRelation Gamma J ⊆ stepPieceGraphs C P := by
  obtain ⟨hθ'pos, hθ'le⟩ := classBudget_pos_le k ht ht1 hg hg1
  set θ' := classBudget theta gamma k
  let Good : Finset (Point N (k + 1) × ZMod N) → Prop := fun G =>
    ∃ P : ClassPiece C Gamma (section16Zeta theta gamma k) θ' θ' (classDelta theta gamma k) θ'
      gamma, G = partialGraph P.D P.phi
  have hmass : 0 < θ' * (N : Real) ^ (k + 1) := by
    have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
    positivity
  obtain ⟨q, G, J, hG, hq, hJ, hcov⟩ := section16_greedy_relation_decomposition Good theta
    (θ' * (N : Real) ^ (k + 1)) hmass Gamma (by
      intro Delta hDelta hproj
      obtain ⟨P⟩ := class_piece_of_subrelation C hk ht ht1 hg hg1 hN hprod Delta hDelta hproj
      refine ⟨partialGraph P.D P.phi, P.graph_sub, ?_, ⟨P.widen C hDelta, rfl⟩⟩
      rw [partialGraph_card]
      exact P.card_ge)
  set m := classPieces gamma theta k with hmdef
  have hqm : q ≤ m := by
    rw [hmdef, classPieces]
    apply Nat.le_floor
    have hNpos : (0 : Real) < (N : Real) ^ (k + 1) := by
      have : (0 : Real) < N := by exact_mod_cast NeZero.pos N
      positivity
    have h1 : (q : Real) * (θ' * (N : Real) ^ (k + 1)) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) :=
      hq.trans hsize
    rw [le_div_iff₀ hθ'pos]
    have h2 : (q : Real) * θ' * (N : Real) ^ (k + 1) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ (k + 1) := by
      linarith [h1]
    exact le_of_mul_le_mul_right h2 hNpos
  choose P hPG using fun i => (hG i).2
  let Q : Fin m → StepPiece C N theta gamma := fun j =>
    if h : j.val < q then ((P ⟨j.val, h⟩).toMassZero C).widen C (Finset.subset_univ _)
    else ClassPiece.empty C _ _ _ _ _ _
  refine ⟨J, hJ, Q, ?_⟩
  intro z hz'
  have hz1 := hcov hz'
  unfold section16FinsetUnion at hz1
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz1
  rw [hPG i] at hi
  refine Finset.mem_biUnion.mpr ⟨⟨i.val, i.isLt.trans_le hqm⟩, Finset.mem_univ _, ?_⟩
  simp only [Q, dif_pos i.isLt]
  exact hi

/-! ### The cover of the next class -/

/-- **Any `n` relations covered by step pieces have one cover**, for any class. -/
theorem class_step_cover_gen (C : UniformClassWith k Thr Cnt Exp) (hk : 1 ≤ k)
    (hCnt : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      1 ≤ Cnt theta gamma n s)
    (hExp : ∀ theta gamma n s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s → s ≤ 1 →
      0 < Exp theta gamma n s ∧ Exp theta gamma n s ≤ 1)
    (hCntMono : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 ≤ s →
      Monotone fun n => Cnt theta gamma n s)
    (hExpAnti : ∀ theta gamma s, 0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 → 0 < s →
      Antitone fun n => Exp theta gamma n s)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n : Nat}
    (Gamma : Fin n → Finset (Point N (k + 1) × ZMod N))
    (P : Fin n → Fin (classPieces gamma theta k) → StepPiece C N theta gamma)
    (hP : ∀ i, Gamma i ⊆ stepPieceGraphs C (P i)) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (clsQr Cnt k M tS gamma) (clsPb Cnt M tS gamma) M rho)
        ((3 ^ (k + 1) * M : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (Cnt tS gS M) (Exp tS gS M) (clsEr Exp k M tS gamma) rho *
          famPieceSliceExponent (clsQr Cnt k M tS gamma) (clsEs Exp M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale A (Cnt tS gS M) (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq (Cnt tS gS M) (Exp tS gS M) (clsEr Exp k M tS gamma) rho)
          (famPieceSliceExponent (clsQr Cnt k M tS gamma) (clsEs Exp M tS gamma) M rho)))
      (Finset.univ.biUnion Gamma) := by
  intro M tS gS
  obtain ⟨htS, htS1⟩ := classBudget_pos_le k ht ht1 hg hg1
  obtain ⟨-, -, hgS, hgS1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  let R : Fin M → StepPiece C N theta gamma := fun c =>
    P (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2
  have hfam := class_piece_family_cover_gen hk C hCnt hExp hCntMono hExpAnti hA hB hlemma6 hz
    hzHalf htS htS1 hgS hgS1 htS htS1 hg hg1 R
  refine MultiplyLinearWith.subset hfam ?_
  intro z hz'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz'
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hP i hi)
  refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.symm_apply_apply]
  exact hc

/-- **Any `n` relations covered by step pieces have one cover.** -/
theorem class_step_cover {V : Real} {dC dE dT : Nat} (C : PowerUniformClass k V dC dE dT)
    (hk : 1 ≤ k) (hV : 1 ≤ V)
    {A Bq : Nat → Real} (hA : ∀ q, 0 < A q) (hB : ∀ q, 0 < Bq q)
    (hlemma6 : AbstractFamilyLemma166At k (section16PowerWidth A Bq))
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] {n : Nat}
    (Gamma : Fin n → Finset (Point N (k + 1) × ZMod N))
    (P : Fin n → Fin (classPieces gamma theta k) → StepPiece C N theta gamma)
    (hP : ∀ i, Gamma i ⊆ stepPieceGraphs C (P i)) :
    let M := n * classPieces gamma theta k
    let tS := classBudget theta gamma k
    let gS := classDelta theta gamma k
    MultiplyLinearWith
      (fun rho => max (famPieceGraphBound (classQr V dC k M tS gamma) (classPb V dC M tS gamma) M rho)
        ((3 ^ (k + 1) * M : Nat) : Real))
      (fun rho => section16CappedWidthExponent
        (pieceLineExponent Bq (classQb V dC M tS gS) (classEb V dE M tS gS)
            (classEr V dE k M tS gamma) rho *
          famPieceSliceExponent (classQr V dC k M tS gamma) (classEs V dE M tS gamma) M rho / 4)
        (section16RoundedPowerThreshold
          (pieceWidthScale A (classQb V dC M tS gS) (section16Zeta theta gamma k) rho)
          (pieceLineExponent Bq (classQb V dC M tS gS) (classEb V dE M tS gS)
            (classEr V dE k M tS gamma) rho)
          (famPieceSliceExponent (classQr V dC k M tS gamma) (classEs V dE M tS gamma) M rho)))
      (Finset.univ.biUnion Gamma) := by
  intro M tS gS
  obtain ⟨htS, htS1⟩ := classBudget_pos_le k ht ht1 hg hg1
  obtain ⟨-, -, hgS, hgS1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  let R : Fin M → StepPiece C N theta gamma := fun c =>
    P (finProdFinEquiv.symm c).1 (finProdFinEquiv.symm c).2
  have hfam := class_piece_family_cover hk hV C hA hB hlemma6 hz hzHalf htS htS1 hgS hgS1
    htS htS1 hg hg1 R
  refine MultiplyLinearWith.subset hfam ?_
  intro z hz'
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz'
  obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.mp (hP i hi)
  refine Finset.mem_biUnion.mpr ⟨finProdFinEquiv (i, c), Finset.mem_univ _, ?_⟩
  simp only [R, Equiv.symm_apply_apply]
  exact hc

end LeanProofs.GowersSzemeredi
