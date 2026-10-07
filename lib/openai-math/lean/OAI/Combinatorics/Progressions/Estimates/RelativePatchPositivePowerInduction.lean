/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.RelativePatchWeightDescent
import OAI.Combinatorics.Progressions.Geometry.RelativePatchFiniteCoordinateReduction
import OAI.Combinatorics.Progressions.Geometry.RelativePatchStageTransport
import OAI.Combinatorics.Progressions.Linear.PreparedUniformShortSourceRankBudget
import OAI.Combinatorics.Progressions.Sampling.PreparedEarlyLateSamplerGeometry

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

theorem integerBox_real_expect_eq_residue {X : Type*} [Fintype X] [DecidableEq X]
    (N : X → ℕ) [∀ i, NeZero (N i)] (f : (X → ℤ) → ℝ) :
    (𝔼 x ∈ integerBox N, f x) = 𝔼 u, f (residueBoxIntegerPoint N u) := by
  symm
  apply Finset.expect_bij (fun u _ => residueBoxIntegerPoint N u)
  · intro u _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by
        change ((u i).val : ℤ) < N i
        exact_mod_cast (u i).val_lt⟩)
  · intro u _
    rfl
  · intro u _ v _ h
    funext i
    apply ZMod.val_injective
    have hi := congrFun h i
    dsimp only [residueBoxIntegerPoint] at hi
    exact_mod_cast hi
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => (x i : ZMod (N i)), Finset.mem_univ _, ?_⟩
    funext i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt (hx' i).1 (hx' i).2]

theorem relativePatchSliceScore_identity {X : Type*} [Fintype X]
    {s d : ℕ} (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (A : PolynomialPatch X s d) :
    relativePatchSliceScore (ResidueBoxSlice.identity N) f a A =
      relativePatchBoxScore N f a A := by
  unfold relativePatchSliceScore relativePatchBoxScore
  simp only [ResidueBoxSlice.identity, ResidueBoxSlice.point, zero_add, one_mul]
  apply Finset.expect_bij (fun t _ i => ((t i).val : ℤ))
  · intro t _
    exact (mem_integerBox N _).mpr (fun i =>
      ⟨Int.natCast_nonneg _, by exact_mod_cast (t i).isLt⟩)
  · intro t _
    simp only [Int.cast_natCast]
  · intro t _ u _ h
    funext i
    apply Fin.ext
    exact_mod_cast congrFun h i
  · intro x hx
    have hx' := (mem_integerBox N x).mp hx
    refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, Finset.mem_univ _, ?_⟩
    funext i
    exact Int.toNat_of_nonneg (hx' i).1

theorem exists_initial_relative_absolute_rule (n₀ : ℕ) [NeZero n₀]
    (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∃ xi : ℝ, 0 < xi ∧
      ∀ {p a : ℝ}, 2 ≤ p → Real.exp (-p) ≤ a →
        RelativePatchAbsoluteRule (k - 2) n₀ ((p + 2) ^ (C + 1)) a ((1 + xi) * a)
          ⌊(p + 2) ^ C⌋₊ := by
  obtain ⟨C, hC, xi, hxi, habs⟩ := exists_absolute_crt_threshold_rule (J := Fin n₀) k hk
  refine ⟨C, hC, xi, hxi, ?_⟩
  intro p a hp ha N hprime hinj _hcomparable hN f hf hfree hmean
  let : ∀ i, NeZero (N i) := fun i => ⟨(hprime i).ne_zero⟩
  let : NeZero (∏ i, N i) := ⟨Finset.prod_ne_zero_iff.mpr (fun i _ => (hprime i).ne_zero)⟩
  let x := (p + 2) ^ C
  let cost := (p + 2) ^ (C + 1)
  have hx : 0 ≤ x := pow_nonneg (by linarith) _
  have hcost : 2 * x ≤ cost := by
    dsimp only [cost]
    rw [pow_succ]
    change 2 * x ≤ x * (p + 2)
    nlinarith
  have hxcost : x ≤ cost := by linarith
  have hmem (u : ∀ i, ZMod (N i)) : residueBoxIntegerPoint N u ∈ integerBox N :=
    (mem_integerBox N _).mpr (fun i => ⟨Int.natCast_nonneg _, by
      change ((u i).val : ℤ) < N i
      exact_mod_cast (u i).val_lt⟩)
  have hf' : ∀ u, f (residueBoxIntegerPoint N u) ∈ Set.Icc (0 : ℝ) 1 := fun u => hf _ (hmem u)
  have hmean' : a ≤ 𝔼 u, f (residueBoxIntegerPoint N u) := by
    rwa [integerBox_real_expect_eq_residue] at hmean
  have hfree' : IntegerVectorAPFree
      (residueBoxIntegerPoint N '' Function.support (fun u => f (residueBoxIntegerPoint N u))) k := by
    have hfreeK : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k := by
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using hfree
    intro z d hd
    obtain ⟨i, hi⟩ := hfreeK z d hd
    refine ⟨i, ?_⟩
    rintro ⟨u, hu, he⟩
    apply hi
    rw [← he]
    exact ⟨hmem u, hu⟩
  obtain ⟨_, d, A, hd, hLip, hscore⟩ := habs hp ha N hprime hinj
    (fun i => (Real.exp_le_exp.mpr hxcost).trans (hN i)) (fun u => f (residueBoxIntegerPoint N u))
    hf' hmean' hfree'
  refine ⟨1, by decide, ResidueBoxSlice.identity N, d, A, ?_, Nat.le_floor hd, ?_, ?_⟩
  · intro i
    change Real.exp (-cost) * (N i : ℝ) ≤ (N i : ℝ)
    exact (mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (by linarith)) (Nat.cast_nonneg _)).trans_eq (one_mul _)
  · have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ x := by
      have hh := Real.log_le_log (by positivity : (0 : ℝ) < 1 + A.kernel.lip)
        (by simpa only [add_comm] using hLip)
      rwa [Real.log_exp] at hh
    unfold relativePatchComplexity
    linarith
  · rw [relativePatchSliceScore_identity]
    unfold relativePatchBoxScore
    let : DecidableEq (Fin n₀) := Classical.decEq _
    rw [integerBox_real_expect_eq_residue]
    apply (Real.exp_le_exp.mpr (neg_le_neg hxcost)).trans
    convert hscore using 1
    congr 1
    congr 1
    exact Subsingleton.elim _ _

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct Classical

namespace ResidueBoxSlice

theorem polynomial_weighted_support {X : Type} {N : X → ℕ} {q : ℕ}
    (S : ResidueBoxSlice N q) (i : X) :
    S.polynomial i ∈ weightedSupportLE (fun _ : X => 1) 1 := by
  apply (mem_weightedSupportLE_iff _ _ _).mpr
  change (S.polynomial i).weightedTotalDegree (1 : X → ℕ) ≤ 1
  rw [MvPolynomial.weightedTotalDegree_one]
  exact S.polynomial_degree i

end ResidueBoxSlice

namespace PolynomialPatch.LowestLayerModel

variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {s D E j R : ℕ} {A : PolynomialPatch X s (D + E)}

omit [Fintype X] [DecidableEq X] in
theorem normalizedOrigin_vector_degree (F : A.LowestLayerModel (j + 1)) :
    DegreeLE (fun _ : X => 1) (j + 1)
      (VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin) := by
  apply (degreeLE_iff_basis_coordinates (Pi.basisFun ℝ (Fin D)) _ _ _).mpr
  intro i
  simpa only [coordinate_ofCoordinates] using
    (mem_weightedSupportLE_iff _ _ _).mp (F.normalizedOrigin_degree i)

theorem exists_actual_prepared_slice (F : A.LowestLayerModel (j + 1))
    {p δ : ℝ} (hp : 0 ≤ p) (hR : 1 ≤ R) (hRp : (R : ℝ) ≤ Real.exp p)
    (hδ : 0 < δ) (N : X → ℕ) (f : (X → ℤ) → ℝ) (a : ℝ)
    (hM : (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) ≤ p)
    (hj : ((j + 1 : ℕ) : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hT : (((j + 1) * D : ℕ) : ℝ) + 1 ≤ p)
    (hshare : (δ / ((((j + 1) * D : ℕ) : ℝ) *
      preparationCoordinateCap (j + 1) D ((j + 1) * D) + 1))⁻¹ ≤ Real.exp p)
    (hN : ∀ i, Real.exp ((p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)) ≤ N i) :
    let budget := (p + 2) ^ (budgetDepthExponent 38 (j + 1) + 7)
    ∃ (q : ℕ) (S : ResidueBoxSlice N q)
      (L : RankPreparationFamily X (Fin D) (j + 1))
      (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
      (err : VectorPolynomial X ℝ (Fin D → ℝ)),
      0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp budget * S.length i) ∧
      (∑ u, (L u).rank) ≤ (j + 1) * D ∧
      L.Sized D ((j + 1) * D) ∧ L.PreparedHeights p R ∧
      (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
      (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ)) R (L u).space (L u).poly) ∧
      (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
      VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D))
        (F.reparam S.polynomial S.polynomial_weighted_support).normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
      (∀ x ∈ integerBox S.length, ∀ i, |eval (fun k => (x k : ℝ)) err i| ≤ δ) ∧
      relativePatchBoxScore N f a A ≤
        relativePatchSliceScore S f a (A.reparam S.polynomial S.polynomial_weighted_support) := by
  classical
  have hdec : decX = (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
  subst decX
  let P := VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin
  have hP : DegreeLE (fun _ : X => 1) (j + 1) P := F.normalizedOrigin_vector_degree
  let score (x : ∀ i, Fin (N i)) :=
    (f (fun i => ((x i).val : ℤ)) - a) * A.value (fun i => ((x i).val : ℝ))
  obtain ⟨q, S, L, ip, c, e, hrank, hsize, hheight, hgood, hq, hqb, hlen,
      hscore, hip, he, hid⟩ :=
    exists_prepared_polynomial_layer_exp P hP hp hR hRp hδ N score
      (by simpa using hM) hj hX (by simpa using hT) (by simpa using hshare) hN
  have hdegree u := (hheight u).1
  obtain ⟨err, herrdeg, hidentity, herr⟩ :=
    prepared_error_polynomial S P hP L hdegree ip hip c e he hid
  refine ⟨q, S, L, ip, c, err, hq, hqb, hlen, ?_, ?_, hheight, ?_, hgood,
    hip, herrdeg, ?_, ?_, ?_⟩
  · simpa using hrank
  · simpa using hsize
  · intro u
    simpa using (preparationCoordinateCap_bounds hsize le_rfl u).1
  · have hn : (F.reparam S.polynomial S.polynomial_weighted_support).normalizedOrigin =
        fun i => MvPolynomial.aeval S.polynomial (F.normalizedOrigin i) :=
      funext (F.reparam_normalizedOrigin S.polynomial S.polynomial_weighted_support)
    rw [hn]
    simpa only [P, substitute_ofCoordinates] using hidentity
  · intro x hx i
    have hx' := (mem_integerBox S.length x).mp hx
    let u : ∀ k, Fin (S.length k) := fun k => ⟨(x k).toNat, by
      have := hx' k
      omega⟩
    have hu : (fun k => ((u k).val : ℝ)) = fun k => (x k : ℝ) := by
      funext k
      dsimp [u]
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (hx' k).1]
    rw [← hu]
    exact herr u i
  · have hparent : relativePatchBoxScore N f a A = 𝔼 x, score x := by
      symm
      unfold relativePatchBoxScore
      apply Finset.expect_bij (fun x _ i => ((x i).val : ℤ))
      · intro x _
        exact (mem_integerBox N _).mpr (fun i =>
          ⟨Int.natCast_nonneg _, by exact_mod_cast (x i).isLt⟩)
      · intro x _
        simp only [score, Int.cast_natCast]
      · intro x _ y _ h
        funext i
        apply Fin.ext
        exact_mod_cast congrFun h i
      · intro x hx
        have hx' := (mem_integerBox N x).mp hx
        refine ⟨fun i => ⟨(x i).toNat, by have := hx' i; omega⟩, Finset.mem_univ _, ?_⟩
        funext i
        exact Int.toNat_of_nonneg (hx' i).1
    rw [hparent]
    simpa only [score, relativePatchSliceScore, PolynomialPatch.reparam_value,
      ResidueBoxSlice.polynomial_eval, Int.cast_natCast] using hscore

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

variable {K X : Type*} [Fintype K] [Fintype X] [DecidableEq K] [DecidableEq X]

theorem unconditionedAbsoluteSample_input
    (s : ℕ) (N : X → ℕ) (P : K → ℕ) [∀ i, NeZero (P i)]
    (z : (X → ℤ) × (Option K × X → ℤ)) (f : (X → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hinj : Function.Injective (fun u : ∀ i, ZMod (P i) =>
      jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z))
    (hinside : ∀ u : ∀ i, ZMod (P i),
      jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z ∈ integerBox N)
    {a : ℝ}
    (hmean : a ≤ 𝔼 u, f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z)) :
    (∀ x ∈ integerBox P, f (jointIntegerPhysicalSite x z) ∈ Set.Icc (0 : ℝ) 1) ∧
      IntegerVectorAPFree
        {x | x ∈ integerBox P ∧ f (jointIntegerPhysicalSite x z) ≠ 0} (s + 2) ∧
      a ≤ 𝔼 x ∈ integerBox P, f (jointIntegerPhysicalSite x z) := by
  have hrep (x : K → ℤ) (hx : x ∈ integerBox P) :
      residueBoxIntegerPoint P (fun i => (x i : ZMod (P i))) = x := by
    funext i
    have hxi := (mem_integerBox P x).mp hx i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hxi.1 hxi.2]
  have hinside' (x : K → ℤ) (hx : x ∈ integerBox P) :
      jointIntegerPhysicalSite x z ∈ integerBox N := by
    simpa only [hrep x hx] using hinside (fun i => (x i : ZMod (P i)))
  have hinj' : Set.InjOn (fun x => jointIntegerPhysicalSite x z)
      (↑(integerBox P) : Set (K → ℤ)) := by
    intro x hx y hy he
    have hres : (fun i => (x i : ZMod (P i))) = (fun i => (y i : ZMod (P i))) :=
      hinj (by simpa only [hrep x hx, hrep y hy] using he)
    calc
      x = residueBoxIntegerPoint P (fun i => (x i : ZMod (P i))) := (hrep x hx).symm
      _ = residueBoxIntegerPoint P (fun i => (y i : ZMod (P i))) :=
        congrArg (residueBoxIntegerPoint P) hres
      _ = y := hrep y hy
  refine ⟨fun x hx => hf _ (hinside' x hx), ?_, ?_⟩
  · apply (joint_sample_progression_free hfree (by omega) z
      (↑(integerBox P) : Set (K → ℤ)) hinj').mono
    intro x hx
    exact ⟨hx.1, hinside' x hx.1, hx.2⟩
  · rw [integerBox_real_expect_eq_residue]
    exact hmean

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3
open VectorPolynomial
open scoped BigOperators TensorProduct

namespace PolynomialPatch.LowestLayerModel

theorem exists_uniform_prepared_slice (s errorPower : ℕ) :
    ∃ inputPower costPower : ℕ, 2 ≤ inputPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X]
        (p : ℝ), 2 ≤ p →
      ∀ (D E j R : ℕ) (A : PolynomialPatch X s (D + E))
        (F : A.LowestLayerModel (j + 1)),
        j + 1 ≤ s → (D : ℝ) ≤ p → (Fintype.card X : ℝ) ≤ p →
        1 ≤ R → (R : ℝ) ≤ Real.exp ((p + 2) ^ errorPower) →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ costPower) ≤ N i) →
      ∃ (q : ℕ) (S : ResidueBoxSlice N q)
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧
          (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧
        L.Sized D ((j + 1) * D) ∧
        L.PreparedHeights ((p + 2) ^ inputPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤
          preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧
        DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D))
          (F.reparam S.polynomial S.polynomial_weighted_support).normalizedOrigin =
            L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ errorPower))) ∧
        relativePatchBoxScore N f target A ≤
          relativePatchSliceScore S f target
            (A.reparam S.polynomial S.polynomial_weighted_support) := by
  obtain ⟨inputPower, costPower, hinputPower, hcostPower, hbudget⟩ :=
    exists_preparation_input_power_budget s errorPower
  refine ⟨inputPower, costPower, hinputPower, hcostPower, ?_⟩
  intro X _ _ p hp D E j R A F hj hD hX hR hRp N f target hN
  obtain ⟨hpPrep, hM, hjPrep, hXPrep, hT, hδ, hshare, hRPrep, hcost⟩ :=
    hbudget p hp (j + 1) D (Fintype.card X) R hj hD hX hRp
  have hexp := Real.exp_le_exp.mpr hcost
  obtain ⟨q, S, L, ip, c, err, hq, hqb, hlen, hrank, hsize, hheight,
      hcoord, hgood, hip, herrdeg, hid, herr, hscore⟩ :=
    F.exists_actual_prepared_slice hpPrep hR hRPrep hδ N f target
      hM hjPrep hXPrep hT hshare (fun i => hexp.trans (hN i))
  refine ⟨q, S, L, ip, c, err, hq, hqb.trans hexp, ?_, hrank, hsize,
    hheight, hcoord, hgood, hip, herrdeg, hid, herr, hscore⟩
  intro i
  exact ⟨(hlen i).1, (hlen i).2.trans
    (mul_le_mul_of_nonneg_right hexp (Nat.cast_nonneg _))⟩

end PolynomialPatch.LowestLayerModel
end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem smoothAffineSample_jointIntegerFrame
    (z : (X → ℤ) × (Option K × X → ℤ)) (u : K → ℤ) :
    smoothAffineSample u (fun i => jointIntegerFrame z i.1 i.2) =
      jointIntegerPhysicalSite u z := by
  funext i
  simp only [smoothAffineSample, jointIntegerFrame, jointIntegerPhysicalSite,
    integerPhysicalSite, Pi.add_apply]
  ring

theorem smoothAffineSample_inside_of_residue_sites
    [Fintype X] [DecidableEq K] [DecidableEq X]
    (P : K → ℕ) [∀ i, NeZero (P i)] (N : X → ℕ)
    (z : (X → ℤ) × (Option K × X → ℤ))
    (hinside : ∀ u : ∀ i, ZMod (P i),
      jointIntegerPhysicalSite (residueBoxIntegerPoint P u) z ∈ integerBox N) :
    ∀ u : integerBox P,
      smoothAffineSample u.val (fun i => jointIntegerFrame z i.1 i.2) ∈ integerBox N := by
  intro u
  rw [smoothAffineSample_jointIntegerFrame]
  have hrep : residueBoxIntegerPoint P (fun i => (u.val i : ZMod (P i))) = u.val := by
    funext i
    have hi := (mem_integerBox P u.val).mp u.property i
    dsimp only [residueBoxIntegerPoint]
    rw [ZMod.val_intCast, Int.emod_eq_of_lt hi.1 hi.2]
  simpa only [hrep] using hinside (fun i => (u.val i : ZMod (P i)))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace BooleanCubeKernel

theorem exists_unconditioned_arbitrary_absolute_family
    (s n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)] (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ) (hσ1 : σ ≤ 1)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ)
    (hN : ∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  let f₀ := fun x => if x ∈ integerBox N then f x else 0
  have hf₀ : ∀ x, f₀ x ∈ Set.Icc (0 : ℝ) 1 := by
    intro x
    by_cases hx : x ∈ integerBox N
    · simpa only [f₀, ite_eq_left hx] using hf x hx
    · simp only [f₀, ite_eq_right hx, Set.mem_Icc, le_refl, zero_le_one, and_self]
  have hmean₀ : a + σ ≤ 𝔼 x ∈ integerBox N, f₀ x := by
    have he : (𝔼 x ∈ integerBox N, f₀ x) = 𝔼 x ∈ integerBox N, f x :=
      Finset.expect_congr rfl (fun x hx => ite_eq_left hx)
    rwa [he]
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hlocal, hinside⟩ :=
    exists_concrete_unconditioned_productive_family P i ha hσ hσ1 N hN f₀ hf₀ hmean₀
  refine ⟨hW, hR, hZ, productive, hmass, hinj, ?_, hinside⟩
  intro z hz
  have hlocal' : a ≤ 𝔼 u : ∀ k, ZMod (P k),
      f (jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val)) := by
    have h := hlocal z hz
    simp only [f₀, ite_eq_left (hinside z _)] at h
    linarith
  obtain ⟨hbound, hAP, hmean⟩ := unconditionedAbsoluteSample_input
    s N P (z.1.val,z.2.val) f hf hfree (hinj z hz) (hinside z) hlocal'
  exact habsolute P hprime hdistinct hcomparable hcutoff
    (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) hbound hAP hmean

theorem exists_unconditioned_arbitrary_absolute_family_of_zero_score
    (s n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
    (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)] (i : X)
    {p a Λ σ : ℝ} (ha : 0 ≤ a) (hσ : 0 < σ)
    (d₀ : ℕ) (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hprime : ∀ k, (P k).Prime) (hdistinct : Function.Injective P)
    (hcomparable : ∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j)
    (hcutoff : ∀ k, Real.exp p ≤ (P k : ℝ))
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (hN : ∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
      (unconditionedSpatialTrimFraction (Fintype.card X) σ) (unconditionedCollisionWidth P σ) ≤ (N j : ℝ))
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (A : PolynomialPatch X s 0)
    (hscore : σ ≤ relativePatchBoxScore N f a A) :
    let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
    let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
    let R := spatialTrimMargin τ N
    ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
    let law := selectedJointReference (trimmedIntegerBox N R)
      (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
    ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
      σ / 4 ≤ law.mass productive ∧
      (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
      (∀ z ∈ productive,
        RelativePatchSliceConclusion s P
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ p) ∧
      ∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
        ∀ u : ∀ k, ZMod (P k),
        jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N := by
  have hmean : a + σ ≤ 𝔼 x ∈ integerBox N, f x :=
    zero_slot_score_mean_lower_bound A N hbox f hσ hscore
  have hσ1 : σ ≤ 1 := by
    have hcap : (𝔼 x ∈ integerBox N, f x) ≤ 1 :=
      Finset.expect_le hbox (fun x hx => (hf x hx).2)
    linarith
  exact exists_unconditioned_arbitrary_absolute_family s n₀ P i ha hσ hσ1 d₀ habsolute
    hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean

end BooleanCubeKernel
end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct Classical

theorem exists_lowest_weight_prepared_patch (s errorPower : ℕ) :
    ∃ inputPower costPower : ℕ, 2 ≤ inputPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X] (p : ℝ), 2 ≤ p →
      ∀ (d R : ℕ) (A : PolynomialPatch X s d), 0 < d →
        relativePatchComplexity A ≤ p → (Fintype.card X : ℝ) ≤ p →
        1 ≤ R → (R : ℝ) ≤ Real.exp ((p + 2) ^ errorPower) →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ costPower) ≤ (N i : ℝ)) →
      ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ j + 1 ≤ s ∧
      ∃ (q : ℕ) (S : ResidueBoxSlice N q),
      let A' := (A.castRank (Nat.add_sub_of_le hD).symm).reparam
        S.polynomial S.polynomial_weighted_support
      ∃ (F : A'.LowestLayerModel (D := D) (E := d - D) (j + 1))
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∀ i : Fin D, A'.weight (i.castAdd (d - D)) = j + 1) ∧
        (∀ i : Fin (d - D), j + 1 < A'.weight (i.natAdd D)) ∧
        A'.kernel.lip = A.kernel.lip ∧
        relativePatchComplexity A' = relativePatchComplexity A ∧
        relativePatchDistinctWeights A' = relativePatchDistinctWeights A ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧ (∑ u, (L u).rank) ≤ s * D ∧
        L.Sized D ((j + 1) * D) ∧ L.PreparedHeights ((p + 2) ^ inputPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ errorPower))) ∧
        relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' ∧
        relativePatchBoxScore N f target A ≤
          relativePatchBoxScore S.length (S.integerPullback f) target A' := by
  obtain ⟨inputPower, costPower, hinputPower, hcostPower, hprepare⟩ :=
    PolynomialPatch.LowestLayerModel.exists_uniform_prepared_slice s errorPower
  refine ⟨inputPower, costPower, hinputPower, hcostPower, ?_⟩
  intro X _ _ p hp d R A hd hA hX hR hRp N f target hN
  obtain ⟨D, m, hD, hDpos, hmpos, hms, hfirst, hrest, hmodel⟩ :=
    A.exists_lowestLayer_prefix hd
  rcases m with _ | j
  · omega
  obtain ⟨F⟩ := hmodel
  let A₀ := A.castRank (Nat.add_sub_of_le hD).symm
  have hDp : (D : ℝ) ≤ p := (Nat.cast_le.mpr hD).trans
    ((relativePatchComplexity_rank_le A).trans hA)
  obtain ⟨q, S, L, ip, c, err, hq, hqb, hlen, hrank, hsize, hheight,
      hcoord, hgood, hip, herrdeg, hid, herr, hscore⟩ :=
    hprepare X p hp D (d - D) j R A₀ F hms hDp hX hR hRp N f target hN
  let A' := A₀.reparam S.polynomial S.polynomial_weighted_support
  have hscore' : relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' := by
    simpa only [A₀, relativePatchBoxScore, PolynomialPatch.castRank_value] using hscore
  refine ⟨D, j, hD, hDpos, hms, q, S,
    F.reparam S.polynomial S.polynomial_weighted_support,
    L, ip, c, err, hq, hqb, hlen, hfirst, hrest, ?_, ?_, ?_, hrank,
    hrank.trans (Nat.mul_le_mul_right D hms), hsize, hheight, hcoord,
    hgood, hip, herrdeg, hid, herr, hscore', ?_⟩
  · exact PolynomialPatch.castRank_kernel_lip A _
  · change ((D + (d - D) : ℕ) : ℝ) +
      Real.log (1 + ((A.castRank (Nat.add_sub_of_le hD).symm).kernel.lip : ℝ)) =
        relativePatchComplexity A
    rw [PolynomialPatch.castRank_kernel_lip, Nat.add_sub_of_le hD]
    rfl
  · exact relativePatchDistinctWeights_castRank A _
  · rwa [relativePatchBoxScore_pullback]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

theorem exists_lowest_weight_early_late_preparation
    (s requiredPower precisionPower : ℕ) :
    ∃ preparationPower costPower : ℕ,
      2 ≤ preparationPower ∧ 2 ≤ costPower ∧
      ∀ (X : Type) [Fintype X] [DecidableEq X] (p : ℝ), 2 ≤ p →
      ∀ (d : ℕ) (A : PolynomialPatch X s d), 0 < d →
        relativePatchComplexity A ≤ p → (Fintype.card X : ℝ) ≤ p →
      ∀ (N : X → ℕ) (f : (X → ℤ) → ℝ) (target : ℝ),
        (∀ i, Real.exp ((p + 2) ^ (max costPower requiredPower + 1)) ≤ (N i : ℝ)) →
      let R := preparedRoundedRank p requiredPower
      ∃ (D j : ℕ) (hD : D ≤ d), 0 < D ∧ j + 1 ≤ s ∧
      ∃ (q : ℕ) (S : ResidueBoxSlice N q),
      let A' := (A.castRank (Nat.add_sub_of_le hD).symm).reparam
        S.polynomial S.polynomial_weighted_support
      ∃ (F : A'.LowestLayerModel (D := D) (E := d - D) (j + 1))
        (L : RankPreparationFamily X (Fin D) (j + 1))
        (ip : Fin D → MvPolynomial X ℤ) (c : Fin D → ℝ)
        (err : VectorPolynomial X ℝ (Fin D → ℝ)),
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + 2) ^ costPower) ∧
        (∀ i, 0 < S.length i ∧ (N i : ℝ) ≤ Real.exp ((p + 2) ^ costPower) * S.length i) ∧
        (∀ i : Fin D, A'.weight (i.castAdd (d - D)) = j + 1) ∧
        (∀ i : Fin (d - D), j + 1 < A'.weight (i.natAdd D)) ∧
        A'.kernel.lip = A.kernel.lip ∧
        relativePatchComplexity A' = relativePatchComplexity A ∧
        relativePatchDistinctWeights A' = relativePatchDistinctWeights A ∧
        (∑ u, (L u).rank) ≤ (j + 1) * D ∧ (∑ u, (L u).rank) ≤ s * D ∧
        L.Sized D ((j + 1) * D) ∧ L.PreparedHeights ((p + 2) ^ preparationPower) R ∧
        (∀ u, Fintype.card (L u).Coord ≤ preparationCoordinateCap (j + 1) D ((j + 1) * D)) ∧
        (∀ u, HasLayerSamplingRank (u.val + 1) (fun i => (S.length i : ℝ))
          R (L u).space (L u).poly) ∧
        (∀ i, (ip i).totalDegree ≤ j + 1) ∧ DegreeLE (fun _ => 1) (j + 1) err ∧
        VectorPolynomial.ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
          L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ (max (requiredPower + 1) precisionPower)))) ∧
        (∀ x ∈ integerBox S.length, ∀ i,
          |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower))) ∧
        relativePatchBoxScore N f target A ≤ relativePatchSliceScore S f target A' ∧
        relativePatchBoxScore N f target A ≤
          relativePatchBoxScore S.length (S.integerPullback f) target A' ∧
        (∀ i, Real.exp ((p + 2) ^ requiredPower) ≤ (S.length i : ℝ)) ∧
        (∀ i, Real.exp (-((p + 2) ^ costPower)) * (N i : ℝ) ≤ (S.length i : ℝ)) ∧
        ∃ (b : ∀ u, Module.Basis (Fin (preparedSamplerTransverse L u)) ℝ
            (euclideanSubspace (L u).space)ᗮ)
          (_o : ∀ u, OrthonormalBasis (PreparedSamplerContinuous L u) ℝ
            (euclideanSubspace (L u).space))
          (bW : ∀ u, Module.Basis (PreparedSamplerContinuous L u) ℤ
            (latticeSection (standardEuclideanLattice (L u).Coord)
              (euclideanSubspace (L u).space))),
          (∀ u, Submodule.span ℤ (Set.range (b u)) =
            projectedIntegerLattice (euclideanSubspace (L u).space)) ∧
          (∀ u z, ‖normalizedOrthogonalChart (euclideanSubspace (L u).space) (b u) z‖ ≤
            Real.exp (allocatedUniformChartLog
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ)) * ‖z‖) ∧
          (∀ u z, ‖(normalizedOrthogonalChart (euclideanSubspace (L u).space) (b u)).symm z‖ ≤
            Real.exp (allocatedUniformChartLog
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ)) * ‖z‖) ∧
          (∀ u, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L u).space) (b u) ∧
            mixedDensityCovolumeRatio (euclideanSubspace (L u).space) (b u) ≤
              Real.exp (allocatedUniformChartLog
                (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ))) ∧
          (∀ u a, ‖(bW u a).val‖ ≤ Real.exp
            (((p + 2) ^ preparationPower +
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) +
              (p + 2) ^ (requiredPower + 1) + 2) ^
                preparedIntegralBasisExponent (j + 1))) ∧
          (∀ u i, (basisAxisScale (b u) i : ℝ) ≤ Real.exp
            (((p + 2) ^ preparationPower +
              (preparationCoordinateCap (j + 1) D ((j + 1) * D) : ℝ) +
              (p + 2) ^ (requiredPower + 1) + 2) ^
                preparedIntegralBasisExponent (j + 1))) := by
  obtain ⟨preparationPower, costPower, hpreparationPower, hcostPower, hprepare⟩ :=
    exists_lowest_weight_prepared_patch s (max (requiredPower + 1) precisionPower)
  refine ⟨preparationPower, costPower, hpreparationPower, hcostPower, ?_⟩
  intro X _ _ p hp d A hd hA hX N f target hN
  let R := preparedRoundedRank p requiredPower
  have hNprep : ∀ i, Real.exp ((p + 2) ^ costPower) ≤ (N i : ℝ) := by
    intro i
    apply (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2)
      ((Nat.le_max_left costPower requiredPower).trans (Nat.le_succ _)))).trans (hN i)
  obtain ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
      hq, hqb, hlen, hfirst, hrest, hLip, hComplexity, hCount, hrank, hsRank,
      hsize, hheight, hcoord, hgood, hip, herrdeg, hid, herr, hscore, hboxScore⟩ :=
    hprepare X p hp d R A hd hA hX (preparedRoundedRank_one_le p requiredPower)
      ((preparedRoundedRank_le_exp hp requiredPower).trans (Real.exp_le_exp.mpr
        (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (Nat.le_max_left _ _))))
      N f target hNprep
  have hprecision : ∀ x ∈ integerBox S.length, ∀ i,
      |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower)) := by
    intro x hx i
    exact (herr x hx i).trans (Real.exp_le_exp.mpr (neg_le_neg
      (pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) (Nat.le_max_right _ _))))
  have hchildren := prepared_source_side_budgets hp (le_refl ((p + 2) ^ requiredPower))
    N S.length hN (fun i => (hlen i).2)
  refine ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
    hq, hqb, hlen, hfirst, hrest, hLip, hComplexity, hCount, hrank, hsRank,
    hsize, hheight, hcoord, hgood, hip, herrdeg, hid, herr, hprecision, hscore, hboxScore,
    hchildren.1, hchildren.2, ?_⟩
  · let M := preparationCoordinateCap (j + 1) D ((j + 1) * D)
    let pLate := (p + 2) ^ preparationPower + (M : ℝ) + (p + 2) ^ (requiredPower + 1)
    have hprep0 : 0 ≤ (p + 2) ^ preparationPower := by positivity
    have hrank0 : 0 ≤ (p + 2) ^ (requiredPower + 1) := by positivity
    have hcap0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
    apply hheight.exists_early_late_sampler_geometry L (pLate := pLate)
      hprep0 (preparedRoundedRank_one_le p requiredPower)
    · dsimp only [pLate]; linarith
    · apply (preparedRoundedRank_le_exp hp requiredPower).trans
      apply Real.exp_le_exp.mpr
      dsimp only [pLate]; linarith
    · exact hsize
    · exact le_rfl
    · dsimp only [pLate]; change (M : ℝ) ≤ _; linarith

end Erdos3

end

section

namespace Erdos3
open VectorPolynomial Module
open scoped BigOperators TensorProduct Classical

def PreparedRelativePatchPowerPassage
    (s n₀ stage : ℕ) (discount : ℝ)
    (requiredPower precisionPower preparationPower passagePower : ℕ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (nX : ℕ), 0 < nX → (nX : ℝ) ≤ p →
    ∀ (N : Fin nX → ℕ),
      (∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (N i : ℝ)) →
    ∀ (f : (Fin nX → ℤ) → ℝ), (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
    ∀ (D E m : ℕ), 0 < D → 0 < m → m ≤ s →
    ∀ (oldPatch : PolynomialPatch (Fin nX) s (D + E))
      (F : oldPatch.LowestLayerModel m),
      (∀ i : Fin E, m < oldPatch.weight (i.natAdd D)) →
      relativePatchComplexity oldPatch ≤ p →
      relativePatchDistinctWeights oldPatch ≤ stage + 1 →
      Real.exp (-p) ≤ relativePatchBoxScore N f a oldPatch →
    ∀ (L : RankPreparationFamily (Fin nX) (Fin D) m),
      L.Sized D (m * D) →
      L.PreparedHeights ((p + 2) ^ preparationPower) (preparedRoundedRank p requiredPower) →
      (∑ j, (L j).rank) ≤ m * D →
      (∀ j, Fintype.card (L j).Coord ≤ preparationCoordinateCap m D (m * D)) →
      (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ))
        (preparedRoundedRank p requiredPower) (L j).space (L j).poly) →
    ∀ (ip : Fin D → MvPolynomial (Fin nX) ℤ) (c : Fin D → ℝ)
      (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ)),
      (∀ i, (ip i).totalDegree ≤ m) → DegreeLE (fun _ => 1) m err →
      ofCoordinates (R := ℝ) (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
        L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c) + err →
      (∀ x ∈ integerBox N, ∀ i,
        |eval (fun k => (x k : ℝ)) err i| ≤ Real.exp (-((p + 2) ^ precisionPower))) →
      RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ)
        (d₀ + s * (D + E)) ((p + 2) ^ passagePower)

def RelativePatchFinPositivePowerRule
    (s n₀ stage : ℕ) (discount : ℝ) (power : ℕ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (nX : ℕ), 0 < nX → (nX : ℝ) ≤ p →
    ∀ (N : Fin nX → ℕ), (∀ i, Real.exp ((p + 2) ^ power) ≤ (N i : ℝ)) →
    ∀ (f : (Fin nX → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
    ∀ (d : ℕ) (A : PolynomialPatch (Fin nX) s d), 0 < d →
      relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage + 1 →
      Real.exp (-p) ≤ relativePatchBoxScore N f a A →
      RelativePatchSliceConclusion s N f ((1 - discount) ^ (stage + 2) * Λ)
        (d₀ + s * d) ((p + 2) ^ power)

theorem exists_relativePatchFinPositivePower_of_prepared
    {s n₀ stage : ℕ} {discount : ℝ}
    (hpassage : ∃ requiredPower precisionPower : ℕ,
      ∀ preparationPower : ℕ, 2 ≤ preparationPower →
        ∃ passagePower : ℕ, 2 ≤ passagePower ∧
          PreparedRelativePatchPowerPassage s n₀ stage discount
            requiredPower precisionPower preparationPower passagePower) :
    ∃ power : ℕ, 2 ≤ power ∧ RelativePatchFinPositivePowerRule s n₀ stage discount power := by
  obtain ⟨requiredPower, precisionPower, hpassage⟩ := hpassage
  obtain ⟨preparationPower, costPower, hprepPower, hcostPower, hprepare⟩ :=
    exists_lowest_weight_early_late_preparation s requiredPower precisionPower
  obtain ⟨passagePower, hpassagePower, hpass⟩ := hpassage preparationPower hprepPower
  let power := max (max costPower requiredPower + 1) (max costPower passagePower + 1)
  have hp1 : max costPower requiredPower + 1 ≤ power := Nat.le_max_left _ _
  have hp2 : max costPower passagePower + 1 ≤ power := Nat.le_max_right _ _
  refine ⟨power, by omega, ?_⟩
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hN f hf hfree d A hd hA hstage hscore
  have hbase : 1 ≤ p + 2 := by linarith
  let g := relativeBoxInput N f
  have hg : ∀ x, g x ∈ Set.Icc (0 : ℝ) 1 := relativeBoxInput_unitInterval N f (by simpa only [mem_integerBox] using hf)
  have hgfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ g x ≠ 0} (s + 2) := by
    simpa only [mem_integerBox] using
      relativeBoxInput_progressionFree N f (by simpa only [mem_integerBox] using hfree)
  have hgscore : Real.exp (-p) ≤ relativePatchBoxScore N g a A := by
    have heq : relativePatchBoxScore N g a A = relativePatchBoxScore N f a A := by
      apply relativePatchBoxScore_congr_input
      intro x hx
      exact relativeBoxInput_eq N f (by simpa only [mem_integerBox] using hx)
    exact hscore.trans_eq heq.symm
  have hNprep : ∀ i, Real.exp ((p + 2) ^ (max costPower requiredPower + 1)) ≤ (N i : ℝ) :=
    fun i => (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase hp1)).trans (hN i)
  obtain ⟨D, j, hD, hDpos, hjs, q, S, F, L, ip, c, err,
    hq, _hqb, hlen, _hfirst, hrest, _hLip, hcomplexity, hcount,
    hrank, _hsrank, hsize, hheight, hcoord, hgood, hip, herrdeg, hid,
    _herrStrong, herr, _hscoreSlice, hscoreBox, _hsourceSides, hfraction, _hgeometry⟩ :=
    hprepare (Fin nX) p hp d A hd hA (by simpa using hX) N g a hNprep
  have hNpass : ∀ i, Real.exp ((p + 2) ^ passagePower) ≤ (S.length i : ℝ) :=
    (prepared_source_side_budgets hp (le_refl ((p + 2) ^ passagePower)) N S.length
      (fun i => (Real.exp_le_exp.mpr (pow_le_pow_right₀ hbase hp2)).trans (hN i))
      (fun i => (hlen i).2)).1
  have hout := hpass p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX S.length hNpass
    (S.integerPullback g) (fun x => hg (S.integerAffine x)) (S.pullback_apFree hq hgfree)
    D (d - D) (j + 1) hDpos (Nat.zero_lt_succ _) hjs _ F hrest
    (hcomplexity.le.trans hA) (hcount.le.trans hstage) (hgscore.trans hscoreBox)
    L hsize hheight hrank hcoord hgood ip c err hip herrdeg hid herr
  have hcomp := RelativePatchSliceConclusion.comp S hq
    (by positivity : 0 ≤ (p + 2) ^ costPower) hfraction hout
  have hsum : (p + 2) ^ costPower + (p + 2) ^ passagePower ≤ (p + 2) ^ power :=
    (prepared_source_cost_add_required hp (le_refl ((p + 2) ^ passagePower))).trans
      (pow_le_pow_right₀ hbase hp2)
  have hrankFinal : d₀ + s * (D + (d - D)) ≤ d₀ + s * d := by
    rw [Nat.add_sub_of_le hD]
  exact (hcomp.mono hrankFinal hsum).congr_input
    (fun x hx => relativeBoxInput_eq N f hx)

end Erdos3

end

section

namespace Erdos3

open scoped Classical

def RelativePatchFinPowerInductionRule (s n₀ stage : ℕ) (discount : ℝ)
    (power : ℕ) : Prop :=
  RelativePatchFinInductionRule s n₀ stage discount
    (fun p => (p + 2) ^ power) (fun p => (p + 2) ^ power)

theorem RelativePatchFinPowerInductionRule.to_general
    {s n₀ stage power : ℕ} {discount : ℝ}
    (h : RelativePatchFinPowerInductionRule s n₀ stage discount power) :
    RelativePatchPowerInductionRule s n₀ stage discount power :=
  RelativePatchFinInductionRule.to_general h

theorem RelativePatchPowerInductionRule.to_fin
    {s n₀ stage power : ℕ} {discount : ℝ}
    (h : RelativePatchPowerInductionRule s n₀ stage discount power) :
    RelativePatchFinPowerInductionRule s n₀ stage discount power :=
  RelativePatchInductionRule.to_fin h

theorem RelativePatchFinPowerInductionRule.mono
    {s n₀ stage power largerPower : ℕ} {discount : ℝ}
    (h : RelativePatchFinPowerInductionRule s n₀ stage discount power)
    (hpower : power ≤ largerPower) :
    RelativePatchFinPowerInductionRule s n₀ stage discount largerPower := by
  apply RelativePatchInductionRule.to_fin
  apply RelativePatchInductionRule.mono h.to_general
  · intro p hp
    exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hpower
  · intro p hp
    exact pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hpower

theorem relativePatchFinPowerInductionRule_of_zero_and_positive
    {s n₀ stage basePower positivePower : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : RelativePatchFinPowerInductionRule s n₀ 0 discount basePower)
    (hpositive : RelativePatchFinPositivePowerRule s n₀ stage discount positivePower) :
    RelativePatchFinPowerInductionRule s n₀ (stage + 1) discount
      (max basePower positivePower) := by
  intro p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hN f hf hfree d A hA hstage hscore
  have hbase : 1 ≤ p + 2 := by linarith
  by_cases hd : d = 0
  · have hcost : (p + 2) ^ basePower ≤ (p + 2) ^ max basePower positivePower :=
      pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
    have hNzero : ∀ i, Real.exp ((p + 2) ^ basePower) ≤ (N i : ℝ) :=
      fun i => (Real.exp_le_exp.mpr hcost).trans (hN i)
    have hzeroWeights : relativePatchDistinctWeights A ≤ 0 :=
      ((relativePatchDistinctWeights_eq_zero_iff A).mpr hd).le
    have hout := hzero p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hNzero
      f hf hfree d A hA hzeroWeights hscore
    exact (hout.later_stage_target hdiscount
      (((Real.exp_pos (-p)).le.trans ha).trans haΛ)
      (Nat.zero_le (stage + 1))).mono le_rfl hcost
  · have hcost : (p + 2) ^ positivePower ≤ (p + 2) ^ max basePower positivePower :=
      pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
    have hNpositive : ∀ i, Real.exp ((p + 2) ^ positivePower) ≤ (N i : ℝ) :=
      fun i => (Real.exp_le_exp.mpr hcost).trans (hN i)
    exact (hpositive p a Λ d₀ hp ha haΛ hΛ habsolute nX hnX hX N hNpositive
      f hf hfree d A (Nat.pos_of_ne_zero hd) hA hstage hscore).mono le_rfl hcost

theorem exists_relativePatchFinPowerInductionRule_of_positive_successors
    {s n₀ : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ 0 discount power)
    (hstep : ∀ stage : ℕ, stage < s → ∀ power : ℕ, 2 ≤ power →
      RelativePatchFinPowerInductionRule s n₀ stage discount power →
      ∃ nextPower : ℕ, 2 ≤ nextPower ∧
        RelativePatchFinPositivePowerRule s n₀ stage discount nextPower) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ s discount power := by
  obtain ⟨basePower, hbasePower, hbase⟩ := hzero
  have hall : ∀ stage : ℕ, stage ≤ s → ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ stage discount power := by
    intro stage
    induction stage with
    | zero =>
        intro _
        exact ⟨basePower, hbasePower, hbase⟩
    | succ stage ih =>
        intro hstage
        obtain ⟨power, hpower, hrule⟩ := ih (by omega)
        obtain ⟨nextPower, hnextPower, hpositive⟩ :=
          hstep stage (by omega) power hpower hrule
        exact ⟨max basePower nextPower, hbasePower.trans (Nat.le_max_left _ _),
          relativePatchFinPowerInductionRule_of_zero_and_positive hdiscount hbase hpositive⟩
  exact hall s le_rfl

theorem exists_relativePatchPowerInductionRule_of_fin_base_positive_successors
    {s n₀ : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchFinPowerInductionRule s n₀ 0 discount power)
    (hstep : ∀ stage : ℕ, stage < s → ∀ power : ℕ, 2 ≤ power →
      RelativePatchPowerInductionRule s n₀ stage discount power →
      ∃ nextPower : ℕ, 2 ≤ nextPower ∧
        RelativePatchFinPositivePowerRule s n₀ stage discount nextPower) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s n₀ s discount power := by
  obtain ⟨power, hpower, hrule⟩ :=
    exists_relativePatchFinPowerInductionRule_of_positive_successors hdiscount hzero
      (fun stage hstage power hpower hrule =>
        hstep stage hstage power hpower hrule.to_general)
  exact ⟨power, hpower, hrule.to_general⟩

theorem exists_relativePatchPowerInductionRule_of_positive_successors
    {s n₀ : ℕ} {discount : ℝ}
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s n₀ 0 discount power)
    (hstep : ∀ stage : ℕ, stage < s → ∀ power : ℕ, 2 ≤ power →
      RelativePatchPowerInductionRule s n₀ stage discount power →
      ∃ nextPower : ℕ, 2 ≤ nextPower ∧
        RelativePatchFinPositivePowerRule s n₀ stage discount nextPower) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s n₀ s discount power := by
  obtain ⟨basePower, hbasePower, hbase⟩ := hzero
  exact exists_relativePatchPowerInductionRule_of_fin_base_positive_successors hdiscount
    ⟨basePower, hbasePower, hbase.to_fin⟩ hstep

end Erdos3

end

end OAI
