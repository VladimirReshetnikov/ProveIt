import OAI.Combinatorics.Progressions.Polynomial.MeasureDegreeZeroTwistTransfer

namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def frozenTorus
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (y : Y → UnitAddCircle) : ℂ :=
  W.mask residue * W.smooth (center, y)

theorem norm_frozenTorus_le
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) (y : Y → UnitAddCircle) :
    ‖W.frozenTorus residue center y‖ ≤ 1 := by
  rw [frozenTorus, norm_mul]
  exact (mul_le_mul (W.mask_bound _) (W.smooth_bound _) (norm_nonneg _) zero_le_one).trans_eq
    (mul_one 1)

theorem frozenTorus_lipschitz
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (center : X → ℝ) :
    LipschitzWith L (W.frozenTorus residue center) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have h := W.smooth_lipschitz.dist_le_mul (center, y) (center, z)
  simp only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] at h
  calc
    _ = ‖W.mask residue‖ * dist (W.smooth (center, y)) (W.smooth (center, z)) := by
      simp only [frozenTorus, dist_eq_norm, ← mul_sub, norm_mul]
    _ ≤ 1 * ((L : ℝ) * dist y z) :=
      mul_le_mul (W.mask_bound _) h dist_nonneg zero_le_one
    _ = _ := one_mul _

theorem frozenTorus_spatial_error
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    (residue : X → ZMod W.modulus) (x center : X → ℝ) (y : Y → UnitAddCircle) :
    ‖W.mask residue * W.smooth (x, y) - W.frozenTorus residue center y‖ ≤
      (L : ℝ) * dist x center := by
  have h := W.smooth_lipschitz.dist_le_mul (x, y) (center, y)
  simp only [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg)] at h
  calc
    _ = ‖W.mask residue‖ * dist (W.smooth (x, y)) (W.smooth (center, y)) := by
      simp only [frozenTorus, dist_eq_norm, ← mul_sub, norm_mul]
    _ ≤ 1 * ((L : ℝ) * dist x center) :=
      mul_le_mul (W.mask_bound _) h dist_nonneg zero_le_one
    _ = _ := one_mul _

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (center : X → ℝ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) : ℂ :=
  W.frozenTorus (fun i => (u i : ZMod W.modulus)) center
    (physicalGridFactorInput W.cover p (fun i => (u i : ℝ)))

theorem eval_sub_frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (center : X → ℝ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (u : X → ℤ) :
    ‖W.eval N p u - W.frozenSpatialEval center p u‖ ≤
      (L : ℝ) * dist (fun i => (u i : ℝ) / N i) center :=
  W.frozenTorus_spatial_error _ _ _ _

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def normalizedVertexRadius {X : Type*} [Fintype X] {q : ℕ}
    (N : X → ℕ) (V : Option (Fin q) × X → ℝ) (s : Finset (Fin q)) : ℝ :=
  ‖fun x => (V (none, x) + ∑ a ∈ s, V (some a, x)) / N x‖

theorem normalizedVertexRadius_nonneg {X : Type*} [Fintype X] {q : ℕ}
    (N : X → ℕ) (V : Option (Fin q) × X → ℝ) (s : Finset (Fin q)) :
    0 ≤ normalizedVertexRadius N V s := norm_nonneg _

theorem normalized_physicalVertex_norm_le {X : Type*} [Fintype X] {q : ℕ}
    (N : X → ℕ) (V : Option (Fin q) × X → ℝ) (s : Finset (Fin q))
    {z : Option (Fin q) × X → ℤ} (hz : z ∈ rectangularWeightIndices 0 V 1) :
    ‖fun x => (physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ℝ) / N x‖ ≤
      normalizedVertexRadius N V s := by
  apply (pi_norm_le_iff_of_nonneg (normalizedVertexRadius_nonneg N V s)).mpr
  intro x
  have hcoord (k : Option (Fin q)) : |(z (k, x) : ℝ)| ≤ V (k, x) :=
    rectangularWeightIndices_zero_bound V hz (k, x)
  have hvertex : |(physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ℝ)| ≤
      V (none, x) + ∑ a ∈ s, V (some a, x) := by
    simp only [physicalCubeVertexValue, standardPhysicalCubeOutput, Sum.elim_inl,
      Sum.elim_inr, Int.cast_add, Int.cast_sum]
    exact (abs_add_le _ _).trans (add_le_add (hcoord none)
      ((Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun a _ => hcoord (some a)))))
  calc
    _ = |(physicalCubeVertexValue (standardPhysicalCubeOutput z) s x : ℝ)| / N x := by
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg (N x) : (0 : ℝ) ≤ N x)]
    _ ≤ (V (none, x) + ∑ a ∈ s, V (some a, x)) / N x :=
      div_le_div_of_nonneg_right hvertex (Nat.cast_nonneg _)
    _ ≤ |(V (none, x) + ∑ a ∈ s, V (some a, x)) / N x| := le_abs_self _
    _ ≤ normalizedVertexRadius N V s := by
      simpa only [Real.norm_eq_abs, normalizedVertexRadius] using
        norm_le_pi_norm (fun x => (V (none, x) + ∑ a ∈ s, V (some a, x)) / (N x : ℝ)) x

namespace NormalizedPolynomialTwist

variable {X : Type*} [Fintype X] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem selected_eval_sub_frozenSpatialEval
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (center : X → ℝ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (modulus : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin q)) X modulus))
    (s : Finset (Fin q)) (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells V z) :
    ‖(∑' z : Option (Fin q) × X → ℤ,
      ((selectedResidueSmoothPMF modulus cells V hV hZ z).toReal : ℂ) *
        W.eval N poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)) -
      ∑' z : Option (Fin q) × X → ℤ,
        ((selectedResidueSmoothPMF modulus cells V hV hZ z).toReal : ℂ) *
          W.frozenSpatialEval center poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)‖ ≤
      (L : ℝ) * (normalizedVertexRadius N V s + ‖center‖) := by
  have h := selectedResidueSmoothPMF_approximation modulus cells V hV hZ (fun _ => 1)
    (fun z => W.eval N poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s))
    (fun z => W.frozenSpatialEval center poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s))
    (mul_nonneg L.coe_nonneg (add_nonneg (normalizedVertexRadius_nonneg N V s) (norm_nonneg center)))
    (fun _ _ => by simp) ?_
  · simpa only [one_mul] using h
  intro z hz
  apply (W.eval_sub_frozenSpatialEval N center poly _).trans
  apply mul_le_mul_of_nonneg_left _ L.coe_nonneg
  rw [dist_eq_norm]
  exact (norm_sub_le _ _).trans
    (add_le_add (normalized_physicalVertex_norm_le N V s hz) le_rfl)

theorem selected_eval_sub_frozenSpatialEval_zero
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (modulus : X → ℕ) (cells : Finset (ColumnResiduePattern (Option (Fin q)) X modulus))
    (s : Finset (Fin q)) (V : Option (Fin q) × X → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells V z) :
    ‖(∑' z : Option (Fin q) × X → ℤ,
      ((selectedResidueSmoothPMF modulus cells V hV hZ z).toReal : ℂ) *
        W.eval N poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)) -
      ∑' z : Option (Fin q) × X → ℤ,
        ((selectedResidueSmoothPMF modulus cells V hV hZ z).toReal : ℂ) *
          W.frozenSpatialEval 0 poly (physicalCubeVertexValue (standardPhysicalCubeOutput z) s)‖ ≤
      (L : ℝ) * normalizedVertexRadius N V s := by
  simpa only [norm_zero, add_zero] using
    W.selected_eval_sub_frozenSpatialEval N 0 poly modulus cells s V hV hZ

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist
open scoped NNReal BigOperators Classical

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def spatialPartitionLaw {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (x : X → ℝ) (hx : ∀ i, |x i| ≤ b) :
    FiniteProbabilityWeights (X → Fin (intervalSiteCount b r)) where
  weight k := ∏ i, intervalSiteWeight b r (k i) (x i)
  nonneg _ := Finset.prod_nonneg (fun i _ => (intervalSiteWeight_range b hr _ _).1)
  total := by
    rw [← Fintype.prod_sum (fun i (k : Fin (intervalSiteCount b r)) =>
      intervalSiteWeight b r k (x i))]
    simp only [intervalSiteWeight_sum hb hr _ (hx _), Finset.prod_const_one]

theorem spatialPartitionLaw_near {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (x : X → ℝ) (hx : ∀ i, |x i| ≤ b) (k : X → Fin (intervalSiteCount b r))
    (hk : (spatialPartitionLaw hb hr x hx).weight k ≠ 0) :
    dist x (fun i => intervalSiteCenter b r (k i)) ≤ 2 * r := by
  apply (dist_pi_le_iff (by positivity : 0 ≤ 2 * r)).mpr
  intro i
  have hi : intervalSiteWeight b r (k i) (x i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hk i (Finset.mem_univ i)
  exact (intervalSiteWeight_near b r (k i) (x i)
    (lt_of_le_of_ne (intervalSiteWeight_range b hr _ _).1 (Ne.symm hi))).le

theorem spatialPartition_error
    (W : NormalizedPolynomialTwist X Y periodCap coverCap L)
    {b r : ℝ} (hb : 0 < b) (hr : 0 < r)
    (residue : X → ZMod W.modulus) (x : X → ℝ) (hx : ∀ i, |x i| ≤ b)
    (y : Y → UnitAddCircle) :
    ‖W.mask residue * W.smooth (x, y) -
      ∑ k : X → Fin (intervalSiteCount b r), vectorIntervalSiteWeight b r k x *
        W.frozenTorus residue (fun i => intervalSiteCenter b r (k i)) y‖ ≤
      2 * (L : ℝ) * r := by
  let law := spatialPartitionLaw hb hr x hx
  have he := law.norm_complexMean_sub_le
    (fun _ => W.mask residue * W.smooth (x, y))
    (fun k => W.frozenTorus residue (fun i => intervalSiteCenter b r (k i)) y)
    (fun _ => 2 * (L : ℝ) * r) (fun k hk =>
      (W.frozenTorus_spatial_error residue x _ y).trans
        ((mul_le_mul_of_nonneg_left (spatialPartitionLaw_near hb hr x hx k hk) L.coe_nonneg).trans_eq
          (by ring)))
  rw [law.complexMean_const, law.mean_const] at he
  simpa only [FiniteProbabilityWeights.complexMean, law, spatialPartitionLaw,
    Complex.ofReal_prod, vectorIntervalSiteWeight] using he

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
