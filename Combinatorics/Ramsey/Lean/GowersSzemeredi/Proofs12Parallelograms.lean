import GowersSzemeredi.Proofs12
import GowersSzemeredi.Proofs14Product
import GowersSzemeredi.Proofs14Arrangements

/-!
# Large second differences yield many parallelogram pairs

This module proves Lemma 12.2.  We transport `Pair N` to `Point N 2` with
the two coordinates exchanged.  Lemma 14.2 (whose proof is Proposition 12.1)
then supplies the product property, and Corollary 14.6 in dimension one gives
the exact `beta^16 * gamma^48 * N^8` bound.  A final injective map turns the
respected general arrangements into the vertical parallelogram pairs of
Section 12.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def lemma122SwapEquiv (N : Nat) : Pair N ≃ Point N 2 where
  toFun z := ![z.2, z.1]
  invFun x := (x 1, x 0)
  left_inv z := by ext <;> simp
  right_inv x := by funext i; fin_cases i <;> simp

private noncomputable def lemma122PointSet {N : Nat} [NeZero N]
    (B : Finset (Pair N)) : Finset (Point N 2) :=
  B.map (lemma122SwapEquiv N).toEmbedding

private def lemma122PointPhi {N : Nat} (phi : Pair N → ZMod N) :
    Point N 2 → ZMod N :=
  fun x => phi ((lemma122SwapEquiv N).symm x)

@[simp] private lemma lemma122_pointSet_mem {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (z : Pair N) :
    lemma122SwapEquiv N z ∈ lemma122PointSet B ↔ z ∈ B := by
  simp [lemma122PointSet]

private lemma lemma122_pointSet_card {N : Nat} [NeZero N]
    (B : Finset (Pair N)) :
    (lemma122PointSet B).card = B.card := by
  simp [lemma122PointSet]

private lemma lemma122_cubeDifference_eq {N : Nat}
    (f : ZMod N → Complex) (z : Pair N) :
    cubeDifference f (lemma122SwapEquiv N z) =
      secondDifference f z.1 z.2 := by
  change cubeDifference f (Fin.cons z.2 (Fin.cons z.1 (fun i ↦ Fin.elim0 i))) =
    secondDifference f z.1 z.2
  rw [cubeDifference_cons, cubeDifference_cons]
  simp only [cubeDifference, List.ofFn_zero, iteratedDifference, secondDifference]

lemma lemma122_fourier_norm_le {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (r : ZMod N) :
    ‖fourier g r‖ ≤ (N : Real) := by
  rw [fourier, ZMod.dft_apply]
  calc
    _ ≤ ∑ _x : ZMod N, (1 : Real) :=
      norm_sum_le_of_le _ fun x _ => by
        simpa only [smul_eq_mul, norm_mul, AddChar.norm_apply, one_mul] using hg x
    _ = (N : Real) := by simp

private lemma lemma122_gamma_le_one {N : Nat} [NeZero N]
    (beta gamma : Real) (f : ZMod N → Complex) (B : Finset (Pair N))
    (phi : Pair N → ZMod N) (hbeta : 0 < beta) (hf : DiscValued f)
    (hcard : (B.card : Real) = beta * (N : Real) ^ 2)
    (hlarge : ∀ z, z ∈ B →
      gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    gamma ≤ 1 := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hBposReal : 0 < (B.card : Real) := by
    rw [hcard]
    positivity
  have hBpos : 0 < B.card := by exact_mod_cast hBposReal
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hBpos
  have hlower := hlarge z hz
  have hdisc : DiscValued (secondDifference f z.1 z.2) :=
    difference_discValued (difference_discValued hf z.1) z.2
  have hupper :
      ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ ≤ (N : Real) := by
    exact lemma122_fourier_norm_le (secondDifference f z.1 z.2) hdisc (phi z)
  nlinarith

private lemma lemma122_point_product_property {N : Nat} [NeZero N]
    (gamma : Real) (f : ZMod N → Complex) (B : Finset (Pair N))
    (phi : Pair N → ZMod N) (hgamma : 0 < gamma) (hf : DiscValued f)
    (hlarge : ∀ z, z ∈ B →
      gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    HasProductProperty (lemma122PointSet B) (lemma122PointPhi phi) gamma := by
  apply lemma_14_2_holds N 2 gamma f (lemma122PointSet B)
    (lemma122PointPhi phi) hgamma hf
  intro x hx
  let z := (lemma122SwapEquiv N).symm x
  have hzx : lemma122SwapEquiv N z = x :=
    (lemma122SwapEquiv N).apply_symm_apply x
  have hzB : z ∈ B := by
    rw [← lemma122_pointSet_mem B z, hzx]
    exact hx
  have hzlarge := hlarge z hzB
  unfold secondDifferenceFourier at hzlarge
  rw [← lemma122_cubeDifference_eq f z] at hzlarge
  simpa only [hzx, lemma122PointPhi, Equiv.symm_apply_apply] using hzlarge

private lemma lemma122_general_arrangement_lower {N : Nat} [NeZero N]
    (beta gamma : Real) (f : ZMod N → Complex) (B : Finset (Pair N))
    (phi : Pair N → ZMod N) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hf : DiscValued f)
    (hcard : (B.card : Real) = beta * (N : Real) ^ 2)
    (hlarge : ∀ z, z ∈ B →
      gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    beta ^ 16 * gamma ^ 48 * (N : Real) ^ 8 ≤
      respectedGeneralArrangementCount 2 (lemma122PointSet B)
        (lemma122PointPhi phi) := by
  have hgamma_one := lemma122_gamma_le_one beta gamma f B phi hbeta hf hcard hlarge
  have hpointCard : ((lemma122PointSet B).card : Real) =
      beta * (N : Real) ^ (1 + 1) := by
    rw [lemma122_pointSet_card, hcard]
  have hproduct := lemma122_point_product_property gamma f B phi hgamma hf hlarge
  simpa using corollary_14_6_holds N 1 beta gamma (lemma122PointSet B)
    (lemma122PointPhi phi) (by norm_num) hbeta hgamma hgamma_one hpointCard hproduct

private def lemma122FirstParallelogram {N : Nat}
    (R : GeneralArrangement N 1 2) : VerticalParallelogram N :=
  ![R.crossSection 0, R.base 0 0, R.base 2 0,
    R.crossSection 2 - R.crossSection 0, R.side 0]

private def lemma122SecondParallelogram {N : Nat}
    (R : GeneralArrangement N 1 2) : VerticalParallelogram N :=
  ![R.crossSection 3, R.base 3 0, R.base 1 0,
    R.crossSection 1 - R.crossSection 3, R.side 0]

private def lemma122ToPair {N : Nat}
    (R : GeneralArrangement N 1 2) :
    VerticalParallelogram N × VerticalParallelogram N :=
  (lemma122FirstParallelogram R, lemma122SecondParallelogram R)

private lemma lemma122_toPair_injective {N : Nat} :
    Function.Injective (lemma122ToPair (N := N)) := by
  intro R S h
  simp only [lemma122ToPair, lemma122FirstParallelogram, lemma122SecondParallelogram,
    Prod.mk.injEq, Matrix.vecCons_inj, and_true] at h
  obtain ⟨⟨h0, hb0, hb2, hw0, hs⟩, h3, hb3, hb1, hw1, -⟩ := h
  rw [h0, sub_left_inj] at hw0
  rw [h3, sub_left_inj] at hw1
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun j => funext fun i => ?_)
    (funext fun j => ?_))
  · fin_cases i; exact hs
  · fin_cases j <;> fin_cases i <;> assumption
  · fin_cases j <;> assumption

lemma lemma122_additiveTuple_two_iff {N : Nat}
    (q : Fin 4 → ZMod N) :
    IsAdditiveTuple (k := 2) q ↔ q 0 + q 1 = q 2 + q 3 := by
  unfold IsAdditiveTuple
  rw [show (Finset.univ.filter (fun i : Fin 4 ↦ (i : Nat) < 2)) =
      {0, 1} by decide]
  rw [show (Finset.univ.filter (fun i : Fin 4 ↦ 2 ≤ (i : Nat))) =
      {2, 3} by decide]
  simp

private def lemma122BoolVertex (b : Bool) : Fin 1 → Bool := fun _ ↦ b

private lemma lemma122_bool_vertex_univ :
    (Finset.univ : Finset (Fin 1 → Bool)) =
      {lemma122BoolVertex false, lemma122BoolVertex true} := by
  decide

private lemma lemma122_cubeValue_one {N : Nat} [NeZero N]
    (phi : Pair N → ZMod N) (R : GeneralArrangement N 1 2) (j : Fin 4) :
    R.cubeValue (lemma122PointPhi phi) j =
      phi (R.crossSection j, R.base j 0) -
        phi (R.crossSection j, R.base j 0 + R.side 0) := by
  unfold GeneralArrangement.cubeValue
  rw [lemma122_bool_vertex_univ]
  have hne : lemma122BoolVertex false ≠ lemma122BoolVertex true := by
    intro h
    have h0 := congrFun h 0
    simp [lemma122BoolVertex] at h0
  rw [Finset.sum_insert (by simpa using hne)]
  simp [lemma122BoolVertex, GeneralArrangement.vertex, GeneralArrangement.cube,
    AxisCube.vertex, AxisCube.base, AxisCube.side, appendCoordinate,
    lemma122PointPhi, lemma122SwapEquiv, boolWeight, countWhere]
  rw [sub_eq_add_neg]

private lemma lemma122_vertex_eq {N : Nat}
    (R : GeneralArrangement N 1 2) (e : Fin 1 → Bool) (j : Fin 4) :
    R.vertex e j = lemma122SwapEquiv N
      (R.crossSection j,
        R.base j 0 + if e 0 then R.side 0 else 0) := by
  funext i
  fin_cases i <;>
    simp [GeneralArrangement.vertex, GeneralArrangement.cube, AxisCube.vertex,
      AxisCube.base, AxisCube.side, appendCoordinate, lemma122SwapEquiv]

private lemma lemma122_vertex_mem_iff {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (R : GeneralArrangement N 1 2)
    (e : Fin 1 → Bool) (j : Fin 4) :
    R.vertex e j ∈ lemma122PointSet B ↔
      (R.crossSection j,
        R.base j 0 + if e 0 then R.side 0 else 0) ∈ B := by
  rw [lemma122_vertex_eq]
  exact lemma122_pointSet_mem B _

private lemma lemma122_toPair_good {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N)
    (R : GeneralArrangement N 1 2)
    (hR : R.IsIn (lemma122PointSet B) ∧
      R.IsRespected (lemma122PointPhi phi)) :
    (lemma122ToPair R).1.IsIn B ∧
      (lemma122ToPair R).2.IsIn B ∧
      (lemma122ToPair R).1.width = (lemma122ToPair R).2.width ∧
      (lemma122ToPair R).1.height = (lemma122ToPair R).2.height ∧
      (lemma122ToPair R).1.value phi = (lemma122ToPair R).2.value phi := by
  rcases hR with ⟨⟨hcross, hvertices⟩, hrespected⟩
  have hmem (b : Bool) (j : Fin 4) :
      (R.crossSection j, R.base j 0 + if b then R.side 0 else 0) ∈ B :=
    (lemma122_vertex_mem_iff B R (lemma122BoolVertex b) j).mp (hvertices _ j)
  have hfalse (j : Fin 4) : (R.crossSection j, R.base j 0) ∈ B := by simpa using hmem false j
  have htrue (j : Fin 4) : (R.crossSection j, R.base j 0 + R.side 0) ∈ B := by
    simpa using hmem true j
  -- both parallelograms have the shape `(x_j, y_j, y_j', x_j' - x_j, side)`
  have hIn (j j' : Fin 4) : VerticalParallelogram.IsIn ![R.crossSection j, R.base j 0,
      R.base j' 0, R.crossSection j' - R.crossSection j, R.side 0] B := by
    simp [VerticalParallelogram.IsIn, VerticalParallelogram.carrier, Finset.insert_subset_iff,
      VerticalParallelogram.x, VerticalParallelogram.y, VerticalParallelogram.y',
      VerticalParallelogram.width, VerticalParallelogram.height, hfalse, htrue]
  have hx := (lemma122_additiveTuple_two_iff R.crossSection).mp hcross
  have hv := (lemma122_additiveTuple_two_iff _).mp hrespected
  simp_rw [lemma122_cubeValue_one] at hv
  refine ⟨hIn 0 2, hIn 3 1, ?_, rfl, ?_⟩
  · change R.crossSection 2 - R.crossSection 0 = R.crossSection 1 - R.crossSection 3
    linear_combination -hx
  · simp only [lemma122ToPair, lemma122FirstParallelogram, lemma122SecondParallelogram,
      VerticalParallelogram.value, VerticalParallelogram.x, VerticalParallelogram.y,
      VerticalParallelogram.y', VerticalParallelogram.width, VerticalParallelogram.height,
      Matrix.cons_val, add_sub_cancel]
    linear_combination hv

private lemma lemma122_arrangement_count_le {N : Nat} [NeZero N]
    (B : Finset (Pair N)) (phi : Pair N → ZMod N) :
    respectedGeneralArrangementCount 2 (lemma122PointSet B)
        (lemma122PointPhi phi) ≤
      parallelogramPairCount B phi := by
  classical
  unfold respectedGeneralArrangementCount parallelogramPairCount countWhere
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  refine Finset.card_le_card_of_injOn lemma122ToPair ?_ ?_
  · intro R hR
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
      true_and] at hR ⊢
    exact lemma122_toPair_good B phi R hR
  · intro R _ S _ hRS
    exact lemma122_toPair_injective hRS

/-- **Lemma 12.2.** Large Fourier coefficients of second differences yield
many equal vertical-parallelogram pairs. -/
theorem lemma_12_2_holds : lemma_12_2 := by
  intro N _ beta gamma f B phi hbeta hgamma hf hcard hlarge
  have hlower := lemma122_general_arrangement_lower beta gamma f B phi
    hbeta hgamma hf hcard hlarge
  have hcount := lemma122_arrangement_count_le B phi
  exact hlower.trans (by exact_mod_cast hcount)

end LeanProofs.GowersSzemeredi
