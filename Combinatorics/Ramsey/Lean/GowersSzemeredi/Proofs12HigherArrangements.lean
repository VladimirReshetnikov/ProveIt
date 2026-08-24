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
  classical
  unfold respectedGeneralArrangementCount respectedArrangementCount countWhere
  apply Finset.card_equiv (lemma123ArrangementEquiv N d)
  intro R
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [lemma123_arrangement_isIn_iff, lemma123_arrangement_isRespected_iff]

private lemma lemma123_additiveTuple_two_iff {N : Nat}
    (q : Fin 4 → ZMod N) :
    IsAdditiveTuple (k := 2) q ↔ q 0 + q 1 = q 2 + q 3 := by
  unfold IsAdditiveTuple
  rw [show (Finset.univ.filter (fun i : Fin 4 ↦ (i : Nat) < 2)) =
      {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 ↦ 2 ≤ (i : Nat))) =
      {2, 3} by decide]
  simp

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
  have hx := congrArg DArrangement.x hPQ
  have hy := congrArg DArrangement.y hPQ
  have hh := congrArg DArrangement.height hPQ
  have hP1x : P.1.x = Q.1.x := by
    simpa [lemma123PairToArrangement, DArrangement.x] using congrFun hx 0
  have hP2x : P.2.x = Q.2.x := by
    simpa [lemma123PairToArrangement, DArrangement.x] using congrFun hx 3
  have hP1y : P.1.y = Q.1.y := by
    simpa [lemma123PairToArrangement, DArrangement.y] using congrFun hy 0
  have hP1y' : P.1.y' = Q.1.y' := by
    simpa [lemma123PairToArrangement, DArrangement.y] using congrFun hy 2
  have hP2y : P.2.y = Q.2.y := by
    simpa [lemma123PairToArrangement, DArrangement.y] using congrFun hy 3
  have hP2y' : P.2.y' = Q.2.y' := by
    simpa [lemma123PairToArrangement, DArrangement.y] using congrFun hy 1
  have hP1width : P.1.width = Q.1.width := by
    have hsum : P.1.x + P.1.width = Q.1.x + Q.1.width := by
      simpa [lemma123PairToArrangement, DArrangement.x] using congrFun hx 2
    rw [hP1x] at hsum
    exact add_left_cancel hsum
  have hP2width : P.2.width = Q.2.width := by
    have hsum : P.2.x + P.2.width = Q.2.x + Q.2.width := by
      simpa [lemma123PairToArrangement, DArrangement.x] using congrFun hx 1
    rw [hP2x] at hsum
    exact add_left_cancel hsum
  have hP1height : P.1.height = Q.1.height := by
    simpa [lemma123PairToArrangement, DArrangement.height] using hh
  have hP2height : P.2.height = Q.2.height := by
    calc
      P.2.height = P.1.height := hP.symm
      _ = Q.1.height := hP1height
      _ = Q.2.height := hQ
  have hfirst : P.1 = Q.1 := by
    funext i
    fin_cases i
    · exact hP1x
    · exact hP1y
    · exact hP1y'
    · exact hP1width
    · exact hP1height
  have hsecond : P.2 = Q.2 := by
    funext i
    fin_cases i
    · exact hP2x
    · exact hP2y
    · exact hP2y'
    · exact hP2width
    · exact hP2height
  exact Prod.ext hfirst hsecond

private lemma lemma123_pairToArrangement_good {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (P : VerticalParallelogram N × VerticalParallelogram N)
    (hP : P.1.IsIn B ∧ P.2.IsIn B ∧
      P.1.width = P.2.width ∧ P.1.height = P.2.height ∧
      P.1.value phi = P.2.value phi) :
    (lemma123PairToArrangement P).IsIn B ∧
      (lemma123PairToArrangement P).IsRespected phi := by
  rcases hP with ⟨hfirstIn, hsecondIn, hwidth, hheight, hvalue⟩
  have h10 : (P.1.x, P.1.y) ∈ B := by
    apply hfirstIn
    simp [VerticalParallelogram.carrier]
  have h11 : (P.1.x, P.1.y + P.1.height) ∈ B := by
    apply hfirstIn
    simp [VerticalParallelogram.carrier]
  have h12 : (P.1.x + P.1.width, P.1.y') ∈ B := by
    apply hfirstIn
    simp [VerticalParallelogram.carrier]
  have h13 : (P.1.x + P.1.width, P.1.y' + P.1.height) ∈ B := by
    apply hfirstIn
    simp [VerticalParallelogram.carrier]
  have h20 : (P.2.x, P.2.y) ∈ B := by
    apply hsecondIn
    simp [VerticalParallelogram.carrier]
  have h21 : (P.2.x, P.2.y + P.2.height) ∈ B := by
    apply hsecondIn
    simp [VerticalParallelogram.carrier]
  have h22 : (P.2.x + P.2.width, P.2.y') ∈ B := by
    apply hsecondIn
    simp [VerticalParallelogram.carrier]
  have h23 : (P.2.x + P.2.width, P.2.y' + P.2.height) ∈ B := by
    apply hsecondIn
    simp [VerticalParallelogram.carrier]
  constructor
  · unfold DArrangement.IsIn
    constructor
    · apply (lemma123_additiveTuple_two_iff _).mpr
      change P.1.x + (P.2.x + P.2.width) =
        (P.1.x + P.1.width) + P.2.x
      rw [hwidth]
      abel
    · intro i
      fin_cases i
      · simpa [lemma123PairToArrangement, DArrangement.x,
          DArrangement.y, DArrangement.height] using And.intro h10 h11
      · rw [← hheight] at h23
        simpa [lemma123PairToArrangement, DArrangement.x,
          DArrangement.y, DArrangement.height] using And.intro h22 h23
      · simpa [lemma123PairToArrangement, DArrangement.x,
          DArrangement.y, DArrangement.height] using And.intro h12 h13
      · rw [← hheight] at h21
        simpa [lemma123PairToArrangement, DArrangement.x,
          DArrangement.y, DArrangement.height] using And.intro h20 h21
  · unfold DArrangement.IsRespected
    apply (lemma123_additiveTuple_two_iff _).mpr
    change
      (phi (P.1.x, P.1.y + P.1.height) - phi (P.1.x, P.1.y)) +
          (phi (P.2.x + P.2.width, P.2.y' + P.1.height) -
            phi (P.2.x + P.2.width, P.2.y')) =
        (phi (P.1.x + P.1.width, P.1.y' + P.1.height) -
            phi (P.1.x + P.1.width, P.1.y')) +
          (phi (P.2.x, P.2.y + P.1.height) - phi (P.2.x, P.2.y))
    unfold VerticalParallelogram.value at hvalue
    rw [← hheight] at hvalue
    linear_combination -hvalue

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
