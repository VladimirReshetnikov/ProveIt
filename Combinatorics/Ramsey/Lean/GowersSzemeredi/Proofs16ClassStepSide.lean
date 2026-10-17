import GowersSzemeredi.Proofs16ClassStep
import GowersSzemeredi.Proofs15ExplicitThresholds
import GowersSzemeredi.Proofs16ClassPiecesSide

/-! Declarations of `Proofs16ClassStep` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase
variable {k : Nat} {Thr : Real → Real → Real} {Cnt Exp : Real → Real → Nat → Real → Real}

/-- The modulus threshold of the step. -/
def classStepThr (Thr : Real → Real → Real) (theta gamma : Real) (k : Nat) : Real :=
  max 3 (max (lemma156ExplicitThreshold k (theta / 2) gamma) (classPieceThr Thr theta gamma k))

/-- The modulus threshold of the step, for power controls. -/
def classStepThreshold (V : Real) (dT : Nat) (theta gamma : Real) (k : Nat) : Real :=
  max 3 (max (lemma156ExplicitThreshold k (theta / 2) gamma) (classPieceThreshold V dT theta gamma k))

theorem classStepThreshold_eq (V : Real) (dT : Nat) (theta gamma : Real) (k : Nat) :
    classStepThreshold V dT theta gamma k =
      classStepThr (fun theta gamma => (V * (2 / (gamma * theta))) ^ dT) theta gamma k := rfl

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

end

end LeanProofs.GowersSzemeredi
