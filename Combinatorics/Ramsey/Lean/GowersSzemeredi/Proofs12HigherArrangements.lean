import GowersSzemeredi.Proofs12Parallelograms
import GowersSzemeredi.Proofs14HigherArrangements

/-!
# Parallelogram pairs yield many higher arrangements

This module proves Lemma 12.3.  A vertical `d`-arrangement is the
one-dimensional instance of a general arrangement, after exchanging the two
ambient coordinates.  Lemma 14.7 therefore supplies the seventh-power
amplification once parallelogram pairs are injected into respected
`2`-arrangements.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def lemma123SwapEquiv (N : Nat) : Pair N ≃ Point N 2 where
  toFun z := ![z.2, z.1]
  invFun x := (x 1, x 0)
  left_inv z := by ext <;> simp
  right_inv x := by funext i; fin_cases i <;> simp

private noncomputable def lemma123PointSet {N : Nat} [NeZero N]
    (B : Finset (Pair N)) : Finset (Point N 2) :=
  B.map (lemma123SwapEquiv N).toEmbedding

private def lemma123PointPhi {N : Nat} (phi : Pair N → ZMod N) :
    Point N 2 → ZMod N :=
  fun x ↦ -phi ((lemma123SwapEquiv N).symm x)

@[simp] private lemma lemma123_pointSet_mem {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (z : Pair N) :
    lemma123SwapEquiv N z ∈ lemma123PointSet B ↔ z ∈ B := by
  simp [lemma123PointSet]

private def lemma123ArrangementEquiv (N d : Nat) :
    GeneralArrangement N 1 d ≃ DArrangement N d where
  toFun R :=
    (R.crossSection, (fun j ↦ R.base j 0), R.side 0)
  invFun A :=
    ((fun _ ↦ A.height), (fun j _ ↦ A.y j), A.x)
  left_inv R := by
    rcases R with ⟨side, base, cross⟩
    apply Prod.ext
    · funext i
      fin_cases i
      rfl
    · apply Prod.ext
      · funext j i
        fin_cases i
        rfl
      · rfl
  right_inv A := by
    rcases A with ⟨x, y, h⟩
    rfl

private lemma lemma123_vertex_eq {N d : Nat}
    (R : GeneralArrangement N 1 d) (e : Fin 1 → Bool)
    (j : Fin (2 * d)) :
    R.vertex e j = lemma123SwapEquiv N
      (R.crossSection j,
        R.base j 0 + if e 0 then R.side 0 else 0) := by
  funext i
  fin_cases i <;>
    simp [GeneralArrangement.vertex, GeneralArrangement.cube, AxisCube.vertex,
      AxisCube.base, AxisCube.side, appendCoordinate, lemma123SwapEquiv]

private lemma lemma123_vertex_mem_iff {N d : Nat} [NeZero N]
    (B : Finset (Pair N)) (R : GeneralArrangement N 1 d)
    (e : Fin 1 → Bool) (j : Fin (2 * d)) :
    R.vertex e j ∈ lemma123PointSet B ↔
      (R.crossSection j,
        R.base j 0 + if e 0 then R.side 0 else 0) ∈ B := by
  rw [lemma123_vertex_eq]
  exact lemma123_pointSet_mem B _

private def lemma123BoolVertex (b : Bool) : Fin 1 → Bool := fun _ ↦ b

private lemma lemma123_bool_vertex_univ :
    (Finset.univ : Finset (Fin 1 → Bool)) =
      {lemma123BoolVertex false, lemma123BoolVertex true} := by
  decide

private lemma lemma123_cubeValue_one {N d : Nat} [NeZero N]
    (phi : Pair N → ZMod N) (R : GeneralArrangement N 1 d)
    (j : Fin (2 * d)) :
    R.cubeValue (lemma123PointPhi phi) j =
      phi (R.crossSection j, R.base j 0 + R.side 0) -
        phi (R.crossSection j, R.base j 0) := by
  unfold GeneralArrangement.cubeValue
  rw [lemma123_bool_vertex_univ]
  have hne : lemma123BoolVertex false ≠ lemma123BoolVertex true := by
    intro h
    have h0 := congrFun h 0
    simp [lemma123BoolVertex] at h0
  rw [Finset.sum_insert (by simpa using hne)]
  simp [lemma123BoolVertex, GeneralArrangement.vertex,
    GeneralArrangement.cube, AxisCube.vertex, AxisCube.base, AxisCube.side,
    appendCoordinate, lemma123PointPhi, lemma123SwapEquiv, boolWeight,
    countWhere]
  abel

private lemma lemma123_arrangement_isIn_iff {N d : Nat} [NeZero N]
    (B : Finset (Pair N)) (R : GeneralArrangement N 1 d) :
    R.IsIn (lemma123PointSet B) ↔
      (lemma123ArrangementEquiv N d R).IsIn B := by
  unfold GeneralArrangement.IsIn DArrangement.IsIn
  change
    (IsAdditiveTuple R.crossSection ∧
      ∀ e j, R.vertex e j ∈ lemma123PointSet B) ↔
    (IsAdditiveTuple R.crossSection ∧ ∀ j,
      (R.crossSection j, R.base j 0) ∈ B ∧
      (R.crossSection j, R.base j 0 + R.side 0) ∈ B)
  constructor
  · rintro ⟨hadd, hmem⟩
    refine ⟨hadd, fun j ↦ ⟨?_, ?_⟩⟩
    · simpa [lemma123BoolVertex] using (lemma123_vertex_mem_iff B R
        (lemma123BoolVertex false) j).mp
        (hmem (lemma123BoolVertex false) j)
    · simpa [lemma123BoolVertex] using (lemma123_vertex_mem_iff B R
        (lemma123BoolVertex true) j).mp
        (hmem (lemma123BoolVertex true) j)
  · rintro ⟨hadd, hmem⟩
    refine ⟨hadd, ?_⟩
    intro e j
    rw [lemma123_vertex_mem_iff]
    cases he : e 0
    · simpa [he] using (hmem j).1
    · simpa [he] using (hmem j).2

private lemma lemma123_arrangement_isRespected_iff {N d : Nat} [NeZero N]
    (phi : Pair N → ZMod N) (R : GeneralArrangement N 1 d) :
    R.IsRespected (lemma123PointPhi phi) ↔
      (lemma123ArrangementEquiv N d R).IsRespected phi := by
  unfold GeneralArrangement.IsRespected DArrangement.IsRespected
  change
    IsAdditiveTuple (fun j ↦ R.cubeValue (lemma123PointPhi phi) j) ↔
      IsAdditiveTuple (fun j ↦
        phi (R.crossSection j, R.base j 0 + R.side 0) -
          phi (R.crossSection j, R.base j 0))
  have hfun :
      (fun j ↦ R.cubeValue (lemma123PointPhi phi) j) =
        fun j ↦ phi (R.crossSection j, R.base j 0 + R.side 0) -
          phi (R.crossSection j, R.base j 0) := by
    funext j
    exact lemma123_cubeValue_one phi R j
  rw [hfun]

private lemma lemma123_arrangement_count_eq {N d : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    respectedGeneralArrangementCount d (lemma123PointSet B)
        (lemma123PointPhi phi) =
      respectedArrangementCount d B phi := by
  unfold respectedGeneralArrangementCount respectedArrangementCount countWhere
  apply Finset.card_equiv (lemma123ArrangementEquiv N d)
  intro R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lemma123_arrangement_isIn_iff, lemma123_arrangement_isRespected_iff]

private def lemma123PairToArrangement {N : Nat}
    (P : VerticalParallelogram N × VerticalParallelogram N) :
    DArrangement N 2 :=
  (![
      P.1.x,
      P.2.x + P.2.width,
      P.1.x + P.1.width,
      P.2.x],
    (![
      P.1.y,
      P.2.y',
      P.1.y',
      P.2.y],
    P.1.height))

private lemma lemma123_pairToArrangement_injective_on {N : Nat}
    {P Q : VerticalParallelogram N × VerticalParallelogram N}
    (hP : P.1.height = P.2.height)
    (hQ : Q.1.height = Q.2.height)
    (hPQ : lemma123PairToArrangement P =
      lemma123PairToArrangement Q) :
    P = Q := by
  simp only [lemma123PairToArrangement, VerticalParallelogram.x, VerticalParallelogram.y,
    VerticalParallelogram.y', VerticalParallelogram.width, VerticalParallelogram.height,
    Prod.mk.injEq, Matrix.vecCons_inj, and_true] at hPQ
  obtain ⟨⟨hx1, hw2, hw1, hx2⟩, ⟨hy1, hy2', hy1', hy2⟩, hh⟩ := hPQ
  rw [hx1, add_right_inj] at hw1
  rw [hx2, add_right_inj] at hw2
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;> fin_cases i <;>
    first | assumption | exact hP.symm.trans (hh.trans hQ)

private lemma lemma123_pairToArrangement_good {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (P : VerticalParallelogram N × VerticalParallelogram N)
    (hP : P.1.IsIn B ∧ P.2.IsIn B ∧
      P.1.width = P.2.width ∧ P.1.height = P.2.height ∧
      P.1.value phi = P.2.value phi) :
    (lemma123PairToArrangement P).IsIn B ∧
      (lemma123PairToArrangement P).IsRespected phi := by
  obtain ⟨h1, h2, hwidth, hheight, hvalue⟩ := hP
  simp only [VerticalParallelogram.IsIn, VerticalParallelogram.carrier, Finset.insert_subset_iff,
    Finset.singleton_subset_iff, ← hheight] at h1 h2
  simp only [VerticalParallelogram.value, ← hheight] at hvalue
  refine ⟨⟨(lemma122_additiveTuple_two_iff _).mpr ?_, fun i => ?_⟩,
    (lemma122_additiveTuple_two_iff _).mpr ?_⟩ <;>
    simp only [lemma123PairToArrangement, DArrangement.x, DArrangement.y, DArrangement.height,
      Matrix.cons_val]
  · linear_combination -hwidth
  · fin_cases i <;> simp [h1, h2]
  · linear_combination -hvalue

private lemma lemma123_parallelogram_count_le {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    parallelogramPairCount B phi ≤ respectedArrangementCount 2 B phi := by
  classical
  unfold parallelogramPairCount respectedArrangementCount countWhere
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  refine Finset.card_le_card_of_injOn lemma123PairToArrangement ?_ ?_
  · intro P hP
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP ⊢
    exact lemma123_pairToArrangement_good B phi P hP
  · intro P hP Q hQ hPQ
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hP hQ
    exact lemma123_pairToArrangement_injective_on
      hP.2.2.2.1 hQ.2.2.2.1 hPQ

/-- **Lemma 12.3.** Many equal vertical-parallelogram pairs yield many
respected `8`-arrangements. -/
theorem lemma_12_3_holds : lemma_12_3 := by
  intro N _ theta B phi hpairs
  by_cases htheta : 0 < theta
  · have hpairsLe : (parallelogramPairCount B phi : Real) ≤
        respectedArrangementCount 2 B phi := by
      exact_mod_cast lemma123_parallelogram_count_le B phi
    have harrangementTwo :
        theta * (N : Real) ^ 8 ≤ respectedArrangementCount 2 B phi :=
      hpairs.trans hpairsLe
    have hgeneralTwo :
        theta * (N : Real) ^ (5 * 1 + 3) ≤
          respectedGeneralArrangementCount 2 (lemma123PointSet B)
            (lemma123PointPhi phi) := by
      rw [lemma123_arrangement_count_eq]
      simpa using harrangementTwo
    have hhigher := lemma_14_7_holds N 1 theta (lemma123PointSet B)
      (lemma123PointPhi phi) htheta hgeneralTwo
    rw [lemma123_arrangement_count_eq] at hhigher
    simpa using hhigher
  · have hthetaNonpos : theta ≤ 0 := le_of_not_gt htheta
    have hthetaPow : theta ^ 7 ≤ 0 :=
      (show Odd 7 by decide).pow_nonpos hthetaNonpos
    exact (mul_nonpos_of_nonpos_of_nonneg hthetaPow (by positivity)).trans
      (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
