import GowersSzemeredi.Proofs16BaseCaseRestriction

/-!
# Finite greedy extraction for Lemma 16.3

This slice chooses a maximum pairwise-disjoint family of the large Freiman
graphs supplied by the one-dimensional restriction module.  Its complement
has small base projection, yielding a large base set on which the relation is
covered by the enumerated graph family.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi.BaseCase

private noncomputable def candidateUnion {N : Nat} [NeZero N]
    (F : Finset (BaseCandidate N)) : Finset (Point N 1 × ZMod N) :=
  F.biUnion candidateGraph

private noncomputable def candidateFamilies {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (alpha : Real) :
    Finset (Finset (BaseCandidate N)) := by
  classical
  exact Finset.univ.filter (CandidateFamily Gamma alpha)

private lemma empty_candidateFamily {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (alpha : Real) :
    CandidateFamily Gamma alpha ∅ := by
  constructor <;> simp

private lemma candidateFamilies_nonempty {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (alpha : Real) :
    (candidateFamilies Gamma alpha).Nonempty := by
  classical
  exact ⟨∅, by simp [candidateFamilies, empty_candidateFamily]⟩

private lemma candidateUnion_subset {N : Nat} [NeZero N]
    {Gamma : Finset (Point N 1 × ZMod N)} {alpha : Real}
    {F : Finset (BaseCandidate N)} (hF : CandidateFamily Gamma alpha F) :
    candidateUnion F ⊆ Gamma := by
  classical
  intro z hz
  rw [candidateUnion, Finset.mem_biUnion] at hz
  obtain ⟨C, hCF, hzC⟩ := hz
  have hgood := hF.1 C hCF
  rw [candidateGraph, partialGraph, Finset.mem_image] at hzC
  obtain ⟨x, hx, rfl⟩ := hzC
  exact hgood.2.1 x hx

private lemma candidate_graphs_pairwise {N : Nat} [NeZero N]
    {Gamma : Finset (Point N 1 × ZMod N)} {alpha : Real}
    {F : Finset (BaseCandidate N)} (hF : CandidateFamily Gamma alpha F) :
    (F : Set (BaseCandidate N)).PairwiseDisjoint candidateGraph := by
  intro C hCF D hDF hCD
  exact hF.2 C hCF D hDF hCD

private lemma candidateUnion_card {N : Nat} [NeZero N]
    {Gamma : Finset (Point N 1 × ZMod N)} {alpha : Real}
    {F : Finset (BaseCandidate N)} (hF : CandidateFamily Gamma alpha F) :
    (candidateUnion F).card = ∑ C ∈ F, C.1.card := by
  classical
  unfold candidateUnion
  rw [Finset.card_biUnion (candidate_graphs_pairwise hF)]
  simp

private lemma candidateFamily_card_bound {N : Nat} [NeZero N]
    {Gamma : Finset (Point N 1 × ZMod N)} {alpha : Real}
    {F : Finset (BaseCandidate N)}
    (hF : CandidateFamily Gamma alpha F) :
    (F.card : Real) * (alpha * N) ≤ Gamma.card := by
  have hsum :
      ∑ C ∈ F, alpha * N ≤ ∑ C ∈ F, (C.1.card : Real) := by
    exact Finset.sum_le_sum fun C hCF => (hF.1 C hCF).1
  have hunion : ((candidateUnion F).card : Real) ≤ Gamma.card := by
    exact_mod_cast Finset.card_le_card (candidateUnion_subset hF)
  calc
    (F.card : Real) * (alpha * N) = ∑ _C ∈ F, alpha * N := by simp
    _ ≤ ∑ C ∈ F, (C.1.card : Real) := hsum
    _ = (candidateUnion F).card := by
      exact_mod_cast (candidateUnion_card hF).symm
    _ ≤ Gamma.card := hunion

private noncomputable def relationSelection {N k : Nat}
    (Gamma : Finset (Point N k × ZMod N)) (x : Point N k) : ZMod N := by
  classical
  exact if hx : ∃ y, (x, y) ∈ Gamma then Classical.choose hx else 0

private lemma relationSelection_graph {N k : Nat}
    (Gamma : Finset (Point N k × ZMod N)) :
    GraphContained (relationProjection Gamma) (relationSelection Gamma) Gamma := by
  classical
  intro x hx
  have hex : ∃ y, (x, y) ∈ Gamma := by
    obtain ⟨z, hzG, hzx⟩ := Finset.mem_image.mp hx
    exact ⟨z.2, by simpa [← hzx] using hzG⟩
  rw [relationSelection, dif_pos hex]
  exact Classical.choose_spec hex

private lemma candidate_disjoint_of_subset_sdiff {N : Nat} [NeZero N]
    {F : Finset (BaseCandidate N)} {Gamma A : Finset (Point N 1 × ZMod N)}
    (hA : A ⊆ Gamma \ candidateUnion F) (C : BaseCandidate N)
    (hC : candidateGraph C ⊆ A) :
    ∀ D, D ∈ F → Disjoint (candidateGraph C) (candidateGraph D) := by
  classical
  intro D hDF
  rw [Finset.disjoint_left]
  intro z hzC hzD
  have hzDiff := hA (hC hzC)
  have hzUnion : z ∈ candidateUnion F := by
    rw [candidateUnion, Finset.mem_biUnion]
    exact ⟨D, hDF, hzD⟩
  exact (Finset.mem_sdiff.mp hzDiff).2 hzUnion

/-- A maximum disjoint family of large Freiman graph pieces leaves fewer than
`theta*N` uncovered base points. -/
private lemma section16_maximal_graph_family {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hprime : N.Prime) (Gamma : Finset (Point N 1 × ZMod N))
    (hrelation : RelationProductProperty gamma Gamma) :
    ∃ F : Finset (BaseCandidate N),
      CandidateFamily Gamma (lemma163Alpha gamma theta) F ∧
      ((relationProjection (Gamma \ candidateUnion F)).card : Real) < theta * N ∧
      (F.card : Real) * (lemma163Alpha gamma theta * N) ≤ Gamma.card := by
  classical
  obtain ⟨F, hFmem, hFmax⟩ := Finset.exists_max_image
    (candidateFamilies Gamma (lemma163Alpha gamma theta)) Finset.card
    (candidateFamilies_nonempty Gamma (lemma163Alpha gamma theta))
  have hF : CandidateFamily Gamma (lemma163Alpha gamma theta) F := by
    simpa [candidateFamilies] using (Finset.mem_filter.mp hFmem).2
  refine ⟨F, hF, ?_, candidateFamily_card_bound hF⟩
  by_contra hsmall
  have hlarge : theta * N ≤
      (relationProjection (Gamma \ candidateUnion F)).card :=
    le_of_not_gt hsmall
  let Delta := Gamma \ candidateUnion F
  let B := relationProjection Delta
  let phi := relationSelection Delta
  have hDeltaRelation : RelationProductProperty gamma Delta := by
    intro A psi hA
    apply hrelation A psi
    intro x hx
    exact Finset.sdiff_subset (hA x hx)
  obtain ⟨C, hC⟩ := section16_product_restriction gamma theta hgamma
    hgammaOne htheta hthetaOne hprime Delta hDeltaRelation B phi hlarge
    (relationSelection_graph Delta)
  have hCgraphDelta : candidateGraph C ⊆ Delta := by
    intro z hz
    rw [candidateGraph, partialGraph, Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact hC.2.1 x hx
  have hCgraphGamma : GraphContained C.1 C.2 Gamma := by
    intro x hx
    exact Finset.sdiff_subset (hC.2.1 x hx)
  have hCorig : IsBaseCandidate Gamma (lemma163Alpha gamma theta) C :=
    ⟨hC.1, hCgraphGamma, hC.2.2⟩
  have hCnonempty : (candidateGraph C).Nonempty := by
    have hCcardPosReal : (0 : Real) < C.1.card :=
      (mul_pos (lemma163Alpha_pos hgamma htheta) (by exact_mod_cast NeZero.pos N)).trans_le
        hC.1
    have hCcardPos : 0 < C.1.card := by exact_mod_cast hCcardPosReal
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hCcardPos
    exact ⟨(x, C.2 x), by
      rw [candidateGraph, partialGraph, Finset.mem_image]
      exact ⟨x, hx, rfl⟩⟩
  have hCnot : C ∉ F := by
    intro hCF
    obtain ⟨z, hzC⟩ := hCnonempty
    have hzDelta := hCgraphDelta hzC
    have hzUnion : z ∈ candidateUnion F := by
      rw [candidateUnion, Finset.mem_biUnion]
      exact ⟨C, hCF, hzC⟩
    exact (Finset.mem_sdiff.mp hzDelta).2 hzUnion
  have hInsert : CandidateFamily Gamma (lemma163Alpha gamma theta) (insert C F) := by
    constructor
    · intro D hD
      rw [Finset.mem_insert] at hD
      rcases hD with rfl | hDF
      · exact hCorig
      · exact hF.1 D hDF
    · intro D hD E hE hDE
      rw [Finset.mem_insert] at hD hE
      rcases hD with hDC | hDF
      · subst D
        rcases hE with hEC | hEF
        · subst E
          exact (hDE rfl).elim
        · exact candidate_disjoint_of_subset_sdiff
            (F := F) (Gamma := Gamma) (A := Delta) Finset.Subset.rfl C
            hCgraphDelta E hEF
      · rcases hE with hEC | hEF
        · subst E
          exact (candidate_disjoint_of_subset_sdiff
            (F := F) (Gamma := Gamma) (A := Delta) Finset.Subset.rfl C
            hCgraphDelta D hDF).symm
        · exact hF.2 D hDF E hEF hDE
  have hInsertMem : insert C F ∈
      candidateFamilies Gamma (lemma163Alpha gamma theta) := by
    simp [candidateFamilies, hInsert]
  have hmax := hFmax (insert C F) hInsertMem
  rw [Finset.card_insert_of_notMem hCnot] at hmax
  omega

private noncomputable def section16GoodBase {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (F : Finset (BaseCandidate N)) :
    Finset (Point N 1) :=
  Finset.univ \ relationProjection (Gamma \ candidateUnion F)

private lemma pointOne_univ_card {N : Nat} [NeZero N] :
    (Finset.univ : Finset (Point N 1)).card = N := by
  simp [ZMod.card]

private lemma section16GoodBase_card {N : Nat} [NeZero N]
    (theta : Real) (Gamma : Finset (Point N 1 × ZMod N))
    (F : Finset (BaseCandidate N))
    (hsmall : ((relationProjection (Gamma \ candidateUnion F)).card : Real) <
      theta * N) :
    (1 - theta) * N ≤ (section16GoodBase Gamma F).card := by
  classical
  have hproj : relationProjection (Gamma \ candidateUnion F) ⊆
      (Finset.univ : Finset (Point N 1)) := Finset.subset_univ _
  have hcardNat := Finset.card_sdiff_add_card_eq_card hproj
  have hcard :
      ((section16GoodBase Gamma F).card : Real) +
          (relationProjection (Gamma \ candidateUnion F)).card = N := by
    exact_mod_cast (by
      simpa [section16GoodBase, pointOne_univ_card] using hcardNat)
  linarith

private lemma restrictedRelation_subset_candidateUnion {N : Nat} [NeZero N]
    (Gamma : Finset (Point N 1 × ZMod N)) (F : Finset (BaseCandidate N)) :
    restrictRelation Gamma (section16GoodBase Gamma F) ⊆ candidateUnion F := by
  classical
  intro z hz
  rw [restrictRelation, Finset.mem_filter] at hz
  by_contra hzUnion
  have hzDelta : z ∈ Gamma \ candidateUnion F :=
    Finset.mem_sdiff.mpr ⟨hz.1, hzUnion⟩
  have hzProj : z.1 ∈ relationProjection (Gamma \ candidateUnion F) := by
    rw [relationProjection, Finset.mem_image]
    exact ⟨z, hzDelta, rfl⟩
  exact (Finset.mem_sdiff.mp hz.2).2 hzProj

private lemma candidateFamily_count_bound {N : Nat} [NeZero N]
    (gamma theta : Real) (hN : 0 < (N : Real))
    (Gamma : Finset (Point N 1 × ZMod N)) (F : Finset (BaseCandidate N))
    (hFcard : (F.card : Real) * (lemma163Alpha gamma theta * N) ≤ Gamma.card)
    (hGamma : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * N) :
    (F.card : Real) * lemma163Alpha gamma theta ≤ gamma ^ (-(2 : Int)) := by
  have h := hFcard.trans hGamma
  apply le_of_mul_le_mul_right _ hN
  calc
    ((F.card : Real) * lemma163Alpha gamma theta) * N =
        (F.card : Real) * (lemma163Alpha gamma theta * N) := by ring
    _ ≤ gamma ^ (-(2 : Int)) * N := h

structure ExtractedBaseFamily (N : Nat) [NeZero N]
    (gamma theta : Real) (Gamma : Finset (Point N 1 × ZMod N)) where
  q : Nat
  B : Fin q → Finset (Point N 1)
  phi : Fin q → Point N 1 → ZMod N
  J : Finset (Point N 1)
  large : ∀ i, lemma163Alpha gamma theta * N ≤ (B i).card
  graphContained : ∀ i, GraphContained (B i) (phi i) Gamma
  freiman : ∀ i, FreimanHom 8 (pointOneDomain (B i)) (pointOneMap (phi i))
  pairwise : ∀ i j, i ≠ j →
    Disjoint (partialGraph (B i) (phi i)) (partialGraph (B j) (phi j))
  count : (q : Real) * lemma163Alpha gamma theta ≤ gamma ^ (-(2 : Int))
  Jcard : (1 - theta) * N ≤ J.card
  cover : restrictRelation Gamma J ⊆
    section16FinsetUnion (fun i => partialGraph (B i) (phi i))

/-- Enumerated form of the maximum-family extraction. -/
noncomputable def section16_extract_base_family {N : Nat} [NeZero N]
    (gamma theta : Real) (hgamma : 0 < gamma) (hgammaOne : gamma ≤ 1)
    (htheta : 0 < theta) (hthetaOne : theta ≤ 1)
    (hprime : N.Prime) (Gamma : Finset (Point N 1 × ZMod N))
    (hGamma : (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * N)
    (hrelation : RelationProductProperty gamma Gamma) :
    ExtractedBaseFamily N gamma theta Gamma := by
  classical
  let hex := section16_maximal_graph_family gamma theta hgamma hgammaOne htheta
    hthetaOne hprime Gamma hrelation
  let F := Classical.choose hex
  have hF : CandidateFamily Gamma (lemma163Alpha gamma theta) F :=
    (Classical.choose_spec hex).1
  have hsmall : ((relationProjection (Gamma \ candidateUnion F)).card : Real) <
      theta * N := (Classical.choose_spec hex).2.1
  have hFcard : (F.card : Real) * (lemma163Alpha gamma theta * N) ≤
      Gamma.card := (Classical.choose_spec hex).2.2
  let e : Fin F.card ≃ {C // C ∈ F} := F.equivFin.symm
  let C : Fin F.card → BaseCandidate N := fun i => (e i).1
  refine
    { q := F.card
      B := fun i => (C i).1
      phi := fun i => (C i).2
      J := section16GoodBase Gamma F
      large := ?_
      graphContained := ?_
      freiman := ?_
      pairwise := ?_
      count := ?_
      Jcard := section16GoodBase_card theta Gamma F hsmall
      cover := ?_ }
  · intro i
    exact (hF.1 (C i) (e i).2).1
  · intro i
    exact (hF.1 (C i) (e i).2).2.1
  · intro i
    exact (hF.1 (C i) (e i).2).2.2
  · intro i j hij
    apply hF.2 (C i) (e i).2 (C j) (e j).2
    intro hC
    apply hij
    exact e.injective (Subtype.ext hC)
  · exact candidateFamily_count_bound gamma theta
      (by exact_mod_cast NeZero.pos N) Gamma F hFcard hGamma
  · intro z hz
    have hzF := restrictedRelation_subset_candidateUnion Gamma F hz
    rw [candidateUnion, Finset.mem_biUnion] at hzF
    obtain ⟨D, hDF, hzD⟩ := hzF
    let i : Fin F.card := e.symm ⟨D, hDF⟩
    rw [section16FinsetUnion, Finset.mem_biUnion]
    refine ⟨i, Finset.mem_univ i, ?_⟩
    have hi : C i = D := by
      dsimp only [C, i]
      rw [e.apply_symm_apply]
    simpa [hi, candidateGraph] using hzD

end LeanProofs.GowersSzemeredi.BaseCase
