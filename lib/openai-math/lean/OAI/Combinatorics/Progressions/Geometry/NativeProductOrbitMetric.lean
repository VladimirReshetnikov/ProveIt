/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Isometry
import OAI.Combinatorics.Progressions.Estimates.RealProductInclusion
import OAI.Combinatorics.Progressions.Geometry.CoordinatewiseLipschitz

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def productMetricBound (d : ι → ℕ) : ℝ≥0 :=
  ∑ i, coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1

variable {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem productInclusionHom_lipschitz (i : ι) :
    letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ i, Fin (d i))) (d i) 1)
      (productInclusionHom D i) := by
  unfold productInclusionHom
  simpa only [Fintype.card_fin, Nat.cast_one] using
    (lipschitz_realificationMap (hnil := (D i).filtration.lowerCentralSeries_eq_bot)
      (hM := (pi D).filtration.lowerCentralSeries_eq_bot)
      (D i).basis (pi D).basis (liePiSingle i) 1 (fun k j => productInclusion_matrix_height D i j k))

theorem productSpaceEquiv_symm_coordinate_lipschitz (i : ι) (y : ∀ j, (D j).Space) :
    letI := (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a => (productSpaceEquiv D).symm (Function.update y i a)) := by
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] L i) := ((D i).basis.baseChange ℝ).finiteDimensional_of_finite
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] (∀ j, L j)) := ((pi D).basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
    ((D i).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := (pi D).metricSpace
  let g : ∀ j, (D j).RealGroup := fun j => (y j).out
  let e := realBCHPiEquiv (fun j => (D j).filtration)
  let u : (pi D).RealGroup := e.symm (Function.update g i 1)
  have hbase : (fun j => (QuotientGroup.mk (g j) : (D j).Space)) = y :=
    funext (fun j => Quotient.out_eq (y j))
  have heval (a : (D i).RealGroup) :
      (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a)) =
        QuotientGroup.mk (productInclusionHom D i a * u) := by
    rw [← hbase, productSpaceEquiv_symm_update_mk]
    have hup : Function.update g i a = Pi.mulSingle i a * Function.update g i 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
      · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
    rw [hup, map_mul, realBCHPiEquiv_symm_single]
  have hm : LipschitzWith 1 (QuotientGroup.mk : (pi D).RealGroup → (pi D).Space) :=
    quotientMetricSpace_lipschitz_mk ((pi D).basis.baseChange ℝ) (pi D).realLattice
      (pi D).realLattice_closed_discrete.1
  have hf := hm.comp ((isometry_mul_right u).lipschitzWith.comp (productInclusionHom_lipschitz D i))
  have hf' : LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
      (fun a : (D i).RealGroup => (productSpaceEquiv D).symm (Function.update y i (QuotientGroup.mk a))) := by
    simpa only [Function.comp_def, one_mul, heval] using hf
  exact rightCosetMetricSpace_lipschitz_lift (D i).realLattice (D i).realLattice_closed_discrete.1 _ hf'

theorem productSpaceEquiv_symm_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D).symm := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  exact lipschitzWith_of_coordinatewise _ _ (fun i y => productSpaceEquiv_symm_coordinate_lipschitz D i y)

theorem productSpaceEquiv_lipschitz :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    LipschitzWith (productMetricBound d) (productSpaceEquiv D) := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (productMetricBound d).coe_nonneg dist_nonneg)).mpr
  intro i
  have hc : coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 ≤ productMetricBound d := by
    have heq : coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 =
        coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 := by
      unfold coordinateLipschitzBound
      congr 1
      ring
    rw [heq]
    unfold productMetricBound
    exact Finset.single_le_sum
      (f := fun j : ι => coordinateLipschitzBound (Fintype.card (Σ k, Fin (d k))) (d j) 1)
      (s := Finset.univ) (fun _ _ => zero_le) (Finset.mem_univ i)
  exact ((productProjection_lipschitz D i).dist_le_mul x y).trans
    (mul_le_mul_of_nonneg_right (show (coordinateLipschitzBound (d i) (Fintype.card (Σ j, Fin (d j))) 1 : ℝ) ≤
      productMetricBound d from hc) dist_nonneg)

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open scoped NNReal BigOperators

theorem productMetricBound_le {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ 2 * p * (p ^ 2 + p + 1) := by
  have hdim : (Fintype.card (Σ i, Fin (d i)) : ℝ) ≤ p ^ 2 :=
    sigma_card_le_budget hp hι (fun i => by simpa only [Fintype.card_fin] using hd i)
  have hC (i : ι) : (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1 : ℝ) ≤
      2 * (p ^ 2 + p + 1) := by
    change ((Fintype.card (Σ j, Fin (d j)) : ℝ) + (d i : ℝ) + 1) * (1 + 1) ≤ _
    nlinarith [hd i]
  unfold productMetricBound
  rw [NNReal.coe_sum]
  calc
    _ ≤ ∑ _ : ι, 2 * (p ^ 2 + p + 1) := Finset.sum_le_sum (fun i _ => hC i)
    _ = (Fintype.card ι : ℝ) * (2 * (p ^ 2 + p + 1)) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ p * (2 * (p ^ 2 + p + 1)) := mul_le_mul_of_nonneg_right hι (by positivity)
    _ = _ := by ring

theorem productMetricBound_le_exp {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) :
    (productMetricBound d : ℝ) ≤ Real.exp ((p + 4) ^ 4) := by
  have hpoly : 2 * p * (p ^ 2 + p + 1) ≤ (p + 4) ^ 4 := by
    nlinarith [sq_nonneg (p ^ 2), mul_nonneg hp (sq_nonneg p)]
  apply (productMetricBound_le d hp hι hd).trans
  exact hpoly.trans (by linarith [Real.add_one_le_exp ((p + 4) ^ 4)])

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem realBCHPiEquiv_symm_lipschitz :
    letI : ∀ i, MetricSpace (D i).RealGroup := fun i =>
      rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
        ((D i).basis.baseChange ℝ)
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    LipschitzWith (productMetricBound d) (realBCHPiEquiv (fun i => (D i).filtration)).symm := by
  let : ∀ i, MetricSpace (D i).RealGroup := fun i =>
    rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] (∀ i, L i)) := ((pi D).basis.baseChange ℝ).finiteDimensional_of_finite
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let := rightMetricSpace_isIsometricSMul (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  apply lipschitzWith_of_coordinatewise
  intro i y
  let e := realBCHPiEquiv (fun j => (D j).filtration)
  let u : (pi D).RealGroup := e.symm (Function.update y i 1)
  have heval (a : (D i).RealGroup) :
      e.symm (Function.update y i a) = productInclusionHom D i a * u := by
    have hup : Function.update y i a = Pi.mulSingle i a * Function.update y i 1 := by
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self, Pi.mul_apply, Pi.mulSingle_eq_same, mul_one]
      · simp only [Function.update_of_ne hji, Pi.mul_apply, Pi.mulSingle_eq_of_ne hji, one_mul]
    rw [hup, map_mul, realBCHPiEquiv_symm_single]
  have h := (isometry_mul_right u).lipschitzWith.comp (productInclusionHom_lipschitz D i)
  change LipschitzWith (coordinateLipschitzBound (Fintype.card (Σ j, Fin (d j))) (d i) 1)
    (fun a => e.symm (Function.update y i a))
  simpa only [Function.comp_def, heval, one_mul] using h

theorem native_product_group_dist_le (a b : (pi D).RealGroup) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : ∀ i,
      letI := rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
        ((D i).basis.baseChange ℝ)
      dist (productProjectionHom D i a) (productProjectionHom D i b) ≤ ρ) :
    letI := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
      ((pi D).basis.baseChange ℝ)
    dist a b ≤ (productMetricBound d : ℝ) * ρ := by
  let : ∀ i, MetricSpace (D i).RealGroup := fun i =>
    rightMetricSpace (hnil := (D i).filtration.realification.lowerCentralSeries_eq_bot)
      ((D i).basis.baseChange ℝ)
  let := rightMetricSpace (hnil := (pi D).filtration.realification.lowerCentralSeries_eq_bot)
    ((pi D).basis.baseChange ℝ)
  let e := realBCHPiEquiv (fun i => (D i).filtration)
  have hpi : dist (e a) (e b) ≤ ρ := (dist_pi_le_iff hρ).mpr h
  have hdist := (realBCHPiEquiv_symm_lipschitz D).dist_le_mul (e a) (e b)
  change dist (e.symm (e a)) (e.symm (e b)) ≤
    (productMetricBound d : ℝ) * dist (e a) (e b) at hdist
  simp only [MulEquiv.symm_apply_apply] at hdist
  exact hdist.trans (mul_le_mul_of_nonneg_left hpi (productMetricBound d).coe_nonneg)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {ι σ : Type*} [Fintype ι]
  {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
  {s : ℕ} {d : ι → ℕ} (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
  {w : σ → ℕ} (g : ∀ i, (D i).filtration.realification.PolynomialOrbit w)
  (N : ℕ) [NeZero N]

theorem productProjection_cyclicOrbitPoint (x : σ → ZMod N) (i : ι) :
    productProjection D i ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x) =
        (D i).cyclicOrbitPoint (g i) N x :=
  congrArg (fun z : (D i).RealGroup => (QuotientGroup.mk z : (D i).Space))
    (NilpotentLieFiltration.piRealOrbit_eval (fun j => (D j).filtration) g
      (fun j => ((x j).val : ℤ)) i)

variable [DecidableEq ι]

theorem productSpaceEquiv_cyclicOrbitPoint (x : σ → ZMod N) :
    productSpaceEquiv D ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x) =
        fun i => (D i).cyclicOrbitPoint (g i) N x :=
  funext (productProjection_cyclicOrbitPoint D g N x)

variable [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]

theorem pi_cyclicOrbitPoint_dist_le (x y : σ → ZMod N) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    (∀ i, dist ((D i).cyclicOrbitPoint (g i) N x)
      ((D i).cyclicOrbitPoint (g i) N y) ≤ ρ) →
    dist ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x)
      ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y) ≤
          (productMetricBound d : ℝ) * ρ := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro hxy
  have hc : dist
      (productSpaceEquiv D ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x))
      (productSpaceEquiv D ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y)) ≤ ρ := by
    simp only [productSpaceEquiv_cyclicOrbitPoint]
    exact (dist_pi_le_iff hρ).mpr hxy
  have h := (productSpaceEquiv_symm_lipschitz D).dist_le_mul
    (productSpaceEquiv D ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x))
    (productSpaceEquiv D ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y))
  simp only [Equiv.symm_apply_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left hc (productMetricBound d).coe_nonneg)

theorem pi_cyclicOrbitPoint_dist_le_exp (x y : σ → ZMod N) {p ρ : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hd : ∀ i, (d i : ℝ) ≤ p) (hρ : 0 ≤ ρ) :
    letI : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
    letI := (pi D).metricSpace
    (∀ i, dist ((D i).cyclicOrbitPoint (g i) N x)
      ((D i).cyclicOrbitPoint (g i) N y) ≤ ρ) →
    dist ((pi D).cyclicOrbitPoint
      (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N x)
      ((pi D).cyclicOrbitPoint
        (NilpotentLieFiltration.piRealOrbit (fun j => (D j).filtration) g) N y) ≤
          Real.exp ((p + 4) ^ 4) * ρ := by
  let : ∀ i, MetricSpace (D i).Space := fun i => (D i).metricSpace
  let := (pi D).metricSpace
  intro hxy
  exact (pi_cyclicOrbitPoint_dist_le D g N x y hρ hxy).trans
    (mul_le_mul_of_nonneg_right (productMetricBound_le_exp d hp hι hd) hρ)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
