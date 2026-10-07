import OAI.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport
import OAI.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalSampleForecastAtom

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X]

noncomputable def forecastNormalizedSpatialCoordinates (base : X → ℤ) (N : X → ℕ)
    (τ : ℝ) (x : X → ℝ) : (Σ _ : X, Unit ⊕ Empty) → ℝ :=
  fun a => 8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ

theorem forecastNormalizedSpatialCoordinates_lipschitz (base : X → ℤ) (N : X → ℕ)
    {τ : ℝ} (hτ : 0 < τ) :
    LipschitzWith ⟨8 / τ, by positivity⟩ (forecastNormalizedSpatialCoordinates base N τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (div_nonneg (by norm_num) hτ.le) dist_nonneg)).mpr
  intro a
  change |8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ -
    8 * (y a.1 - (base a.1 : ℝ) / N a.1) / τ| ≤ (8 / τ) * dist x y
  rw [show 8 * (x a.1 - (base a.1 : ℝ) / N a.1) / τ -
    8 * (y a.1 - (base a.1 : ℝ) / N a.1) / τ = (8 / τ) * (x a.1 - y a.1) by ring,
    abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 / τ)]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist x y a.1) (by positivity)

omit [Fintype X] in
theorem forecastNormalizedSpatialCoordinates_eval (base u : X → ℤ) (N : X → ℕ)
    (τ : ℝ) (a : Σ _ : X, Unit ⊕ Empty) :
    forecastNormalizedSpatialCoordinates base N τ (fun i => (u i : ℝ) / N i) a =
      ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8) := by
  unfold forecastNormalizedSpatialCoordinates
  ring

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (P : LayerSamplerAxis I n → Prop)
variable {A : Type*} [Fintype A] (selected : A → Σ j : Fin m, Fin (n j))
variable (R : Fin m → ℝ)

def forecastNormalizedInactiveCoordinates (v : LayerSamplerAxis I n → ℝ) : A → ℝ :=
  fun a => R (selected a).1 * v ⟨(selected a).1, Sum.inr (selected a).2⟩

theorem forecastNormalizedInactiveCoordinates_lipschitz
    (hR : ∀ a, |R (selected a).1| ≤ 1) :
    LipschitzWith 1 (forecastNormalizedInactiveCoordinates (I := I) selected R) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  change |R (selected a).1 * v _ - R (selected a).1 * w _| ≤ dist v w
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul_of_nonneg_right (hR a) (abs_nonneg _)).trans
    (by simpa only [one_mul, Real.dist_eq] using dist_le_pi_dist v w ⟨(selected a).1, Sum.inr (selected a).2⟩)

def forecastNormalizedActiveCoordinates (v : LayerSamplerAxis I n → ℝ) :
    (Σ _a : {a : LayerSamplerAxis I n // ¬P a}, Unit) → ℝ := fun a => v a.1.val

theorem forecastNormalizedActiveCoordinates_lipschitz :
    LipschitzWith 1 (forecastNormalizedActiveCoordinates P) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  exact (dist_pi_le_iff dist_nonneg).mpr (fun a => dist_le_pi_dist v w a.1.val)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)

omit [∀ j, Fintype (I j)] [Fintype A] in
theorem forecastNormalizedInactiveCoordinates_mixed
    (hR : ∀ j, R j ≠ 0) (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNormalizedInactiveCoordinates selected R
      (allocatedFullMixedSiteValue (R := R) U b w) =
      fun a => ((w (selected a).1).2 (selected a).2 : ℝ) /
        basisAxisScale (b (selected a).1) (selected a).2 := by
  funext a
  change R (selected a).1 * (_ / _ / R (selected a).1) = _
  rw [mul_div_cancel₀ _ (hR (selected a).1)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (L : ℕ)

local notation "Output" => (Σ _a : {a : LayerSamplerAxis I n //
  ¬allocatedShortAxis (I := I) U basis L a}, Unit)
local notation "ContinuousAxis" => (Σ j : Fin m, I j)
local notation "IntegerAxis" => AllocatedActiveIntegerAxis U basis L

def forecastActiveAxisEquiv : Output ≃ ContinuousAxis ⊕ IntegerAxis where
  toFun a := match a with
    | ⟨⟨⟨j, Sum.inl i⟩, _⟩, _⟩ => Sum.inl ⟨j, i⟩
    | ⟨⟨⟨j, Sum.inr i⟩, h⟩, _⟩ => Sum.inr ⟨⟨j, i⟩, Nat.lt_of_not_ge h⟩
  invFun a := match a with
    | Sum.inl ⟨j, i⟩ => ⟨⟨⟨j, Sum.inl i⟩, not_false⟩, ()⟩
    | Sum.inr a => ⟨⟨⟨a.val.1, Sum.inr a.val.2⟩, Nat.not_le.mpr a.property⟩, ()⟩
  left_inv a := by
    rcases a with ⟨⟨⟨j, i | i⟩, ha⟩, u⟩ <;> cases u <;> rfl
  right_inv a := by
    rcases a with ⟨j, i⟩ | ⟨⟨j, i⟩, ha⟩ <;> rfl

def forecastActiveCoordinateJoin (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) :
    Output → ℝ :=
  fun a => Sum.elim c z (forecastActiveAxisEquiv (I := I) U basis L a)

omit [∀ j, Fintype (I j)] in
theorem forecastActiveCoordinateJoin_continuous
    (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) (a : ContinuousAxis) :
    forecastActiveCoordinateJoin U basis L c z
      ((forecastActiveAxisEquiv U basis L).symm (.inl a)) = c a := by
  simp only [forecastActiveCoordinateJoin, Equiv.apply_symm_apply, Sum.elim_inl]

omit [∀ j, Fintype (I j)] in
theorem forecastActiveCoordinateJoin_integer
    (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) (a : IntegerAxis) :
    forecastActiveCoordinateJoin U basis L c z
      ((forecastActiveAxisEquiv U basis L).symm (.inr a)) = z a := by
  simp only [forecastActiveCoordinateJoin, Equiv.apply_symm_apply, Sum.elim_inr]

theorem forecastActiveCoordinateJoin_lipschitz (c : ContinuousAxis → ℝ) :
    LipschitzWith 1 (forecastActiveCoordinateJoin U basis L c) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  unfold forecastActiveCoordinateJoin
  cases forecastActiveAxisEquiv U basis L a with
  | inl i => simpa only [Sum.elim_inl, dist_self] using (dist_nonneg : 0 ≤ dist z w)
  | inr i => exact dist_le_pi_dist z w i

theorem forecastActiveCoordinateJoin_joint_lipschitz :
    LipschitzWith 1 (fun p : (ContinuousAxis → ℝ) × (IntegerAxis → ℝ) =>
      forecastActiveCoordinateJoin U basis L p.1 p.2) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  unfold forecastActiveCoordinateJoin
  cases forecastActiveAxisEquiv U basis L a with
  | inl i => exact (dist_le_pi_dist p.1 q.1 i).trans (le_max_left _ _)
  | inr i => exact (dist_le_pi_dist p.2 q.2 i).trans (le_max_right _ _)

theorem forecastActiveCoordinateJoin_joint_continuous :
    Continuous (fun p : (ContinuousAxis → ℝ) × (IntegerAxis → ℝ) =>
      forecastActiveCoordinateJoin U basis L p.1 p.2) :=
  (forecastActiveCoordinateJoin_joint_lipschitz U basis L).continuous

theorem forecastActiveCoordinateJoin_norm_le (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) :
    ‖forecastActiveCoordinateJoin U basis L c z‖ ≤ max ‖c‖ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg ((norm_nonneg c).trans (le_max_left _ _))).mpr
  intro a
  unfold forecastActiveCoordinateJoin
  cases forecastActiveAxisEquiv U basis L a with
  | inl i => exact (norm_le_pi_norm c i).trans (le_max_left _ _)
  | inr i => exact (norm_le_pi_norm z i).trans (le_max_right _ _)

theorem forecastActiveCoordinateJoin_continuous_norm_le
    (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) :
    ‖c‖ ≤ ‖forecastActiveCoordinateJoin U basis L c z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro a
  have h := norm_le_pi_norm (forecastActiveCoordinateJoin U basis L c z)
    ((forecastActiveAxisEquiv U basis L).symm (.inl a))
  simpa only [forecastActiveCoordinateJoin_continuous] using h

theorem forecastActiveCoordinateJoin_integer_norm_le
    (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) :
    ‖z‖ ≤ ‖forecastActiveCoordinateJoin U basis L c z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro a
  have h := norm_le_pi_norm (forecastActiveCoordinateJoin U basis L c z)
    ((forecastActiveAxisEquiv U basis L).symm (.inr a))
  simpa only [forecastActiveCoordinateJoin_integer] using h

theorem forecastActiveCoordinateJoin_norm (c : ContinuousAxis → ℝ) (z : IntegerAxis → ℝ) :
    ‖forecastActiveCoordinateJoin U basis L c z‖ = max ‖c‖ ‖z‖ :=
  le_antisymm (forecastActiveCoordinateJoin_norm_le U basis L c z)
    (max_le (forecastActiveCoordinateJoin_continuous_norm_le U basis L c z)
      (forecastActiveCoordinateJoin_integer_norm_le U basis L c z))

omit [∀ j, Fintype (I j)] in
theorem forecastActiveCoordinateJoin_mixed (R : Fin m → ℝ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNormalizedActiveCoordinates (allocatedShortAxis (I := I) U basis L)
        (allocatedFullMixedSiteValue (R := R) U basis w) =
      forecastActiveCoordinateJoin U basis L
        (fun a => (w a.1).1 a.2 / R a.1)
        (fun a => ((w a.val.1).2 a.val.2 : ℝ) /
          allocatedActiveIntegerGridScale U basis R L a) := by
  funext a
  rcases a with ⟨⟨⟨j, i | i⟩, ha⟩, u⟩
  · rfl
  · change ((w j).2 i : ℝ) / (basisAxisScale (basis j) i : ℝ) / R j =
      ((w j).2 i : ℝ) / (R j * (basisAxisScale (basis j) i : ℝ))
    rw [div_div, mul_comm (R j)]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical NNReal BigOperators

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

noncomputable def forecastNativeMixedRow (j : Fin m) :
    (LayerSamplerAxis I n → ℝ) →ₗ[ℝ] ((I j → ℝ) × (Fin (n j) → ℝ)) :=
  ((R j) • LinearMap.pi (fun i : I j => LinearMap.proj ⟨j, Sum.inl i⟩)).prod
    ((R j) • LinearMap.pi (fun i : Fin (n j) => LinearMap.proj ⟨j, Sum.inr i⟩))

noncomputable def forecastNativeAmbientLinear :
    (LayerSamplerAxis I n → ℝ) →ₗ[ℝ] ((Σ j, J j) → ℝ) :=
  LinearMap.pi (fun a => (LinearMap.proj a.2).comp
    ((EuclideanSpace.equiv (J a.1) ℝ).toLinearMap.comp
      ((mixedRealPoint (euclideanSubspace (U a.1)) (b a.1) (o a.1)).comp
        (forecastNativeMixedRow (I := I) (n := n) R a.1))))

noncomputable def forecastNativeAmbientLip : ℝ≥0 :=
  ‖(forecastNativeAmbientLinear U b o R).toContinuousLinearMap‖₊

theorem forecastNativeAmbientLinear_lipschitz :
    LipschitzWith (forecastNativeAmbientLip U b o R) (forecastNativeAmbientLinear U b o R) :=
  (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.lipschitzWith

theorem forecastNativeAmbientLinear_mixed (hR : ∀ j, R j ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNativeAmbientLinear U b o R (allocatedFullMixedSiteValue (R := R) U b w) =
      fun a : Σ j, J j => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 := by
  have hrow (j : Fin m) : forecastNativeMixedRow (I := I) (n := n) R j
      (allocatedFullMixedSiteValue (R := R) U b w) =
      ((w j).1, fun i => ((w j).2 i : ℝ) / basisAxisScale (b j) i) := by
    apply Prod.ext <;> funext i
    · change R j * ((w j).1 i / R j) = _
      exact mul_div_cancel₀ _ (hR j)
    · change R j * ((((w j).2 i : ℝ) / basisAxisScale (b j) i) / R j) = _
      exact mul_div_cancel₀ _ (hR j)
  funext a
  change mixedRealPoint _ _ _ (forecastNativeMixedRow R a.1 _) a.2 = _
  rw [hrow, mixedRealPoint_integer]

variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
local notation "Active" => {a : LayerSamplerAxis I n // ¬P a}
local notation "Output" => (Σ _a : Active, Unit)

def forecastNativeFillAxes (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (v : Output → ℝ) : LayerSamplerAxis I n → ℝ :=
  fun a => if ha : P a then frozen ⟨a, ha⟩ else v ⟨⟨a, ha⟩, ()⟩

theorem forecastNativeFillAxes_lipschitz (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith 1 (forecastNativeFillAxes P frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro a
  by_cases ha : P a
  · simp only [forecastNativeFillAxes, ha, ↓reduceDIte, dist_self, dist_nonneg]
  · simpa only [forecastNativeFillAxes, ha, ↓reduceDIte] using dist_le_pi_dist v w ⟨⟨a, ha⟩, ()⟩

omit [∀ j, Fintype (I j)] in
theorem forecastNativeFillAxes_restrict (v : LayerSamplerAxis I n → ℝ) :
    forecastNativeFillAxes P (fun a => v a.val) (fun a => v a.1.val) = v := by
  funext a
  simp only [forecastNativeFillAxes]
  split <;> rfl

variable {X : Type*} [Fintype X]
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))

noncomputable def forecastNativeSpatialInverse (center : X → ℝ) (τ : ℝ) (z : Spatial → ℝ) : X → ℝ :=
  fun x => center x + τ / 8 * z ⟨x, Sum.inl ()⟩

theorem forecastNativeSpatialInverse_lipschitz (center : X → ℝ) (τ : ℝ) :
    LipschitzWith ‖τ / 8‖₊ (forecastNativeSpatialInverse center τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (mul_nonneg (norm_nonneg _) dist_nonneg)).mpr
  intro x
  change dist (center x + τ / 8 * z ⟨x, Sum.inl ()⟩)
    (center x + τ / 8 * w ⟨x, Sum.inl ()⟩) ≤ _
  rw [dist_add_left, dist_eq_norm, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left (dist_le_pi_dist z w _) (norm_nonneg _)

omit [Fintype X] in
theorem forecastNativeSpatialInverse_integer (base u : X → ℤ) (N : X → ℕ)
    (hN : ∀ x, 0 < N x) {τ : ℝ} (hτ : τ ≠ 0) :
    forecastNativeSpatialInverse (fun x => (base x : ℝ) / N x) τ
      (fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)) =
      fun x => (u x : ℝ) / N x := by
  funext x
  have hn : (N x : ℝ) ≠ 0 := by exact_mod_cast (hN x).ne'
  dsimp only [forecastNativeSpatialInverse]
  field_simp
  ring

noncomputable def forecastNativeTorusInverse (d : ℕ) [NeZero d]
    (deck : (Σ j, J j) → ZMod d)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) (v : Output → ℝ) :
    (Σ j, J j) → UnitAddCircle :=
  fun a => ((forecastNativeAmbientLinear U b o R (forecastNativeFillAxes P frozen v) a /
    d : ℝ) : UnitAddCircle) + ZMod.toAddCircle (deck a)

theorem forecastNativeTorusInverse_lipschitz (d : ℕ) [NeZero d]
    (deck : (Σ j, J j) → ZMod d)
    (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (forecastNativeAmbientLip U b o R)
      (forecastNativeTorusInverse U b o R P d deck frozen) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have h := ((forecastNativeAmbientLinear_lipschitz U b o R).comp
    (forecastNativeFillAxes_lipschitz P frozen)).dist_le_mul v w
  simp only [mul_one] at h
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  rw [forecastNativeTorusInverse, forecastNativeTorusInverse, dist_add_right,
    dist_eq_norm, ← AddCircle.coe_sub]
  apply QuotientAddGroup.norm_mk_le_norm.trans
  rw [← sub_div, norm_div]
  have hd : (1 : ℝ) ≤ ‖(d : ℝ)‖ := by
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  exact (div_le_self (norm_nonneg _) hd).trans
    ((dist_le_pi_dist _ _ a).trans h)

theorem forecastNativeTorusInverse_mixed (hR : ∀ j, R j ≠ 0)
    (d : ℕ) [NeZero d] (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
    (β : (Σ j, J j) → ℤ) :
    forecastNativeTorusInverse U b o R P d (fun a => (β a : ZMod d))
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      fun a : Σ j, J j => (((normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 + β a) / d : ℝ) : UnitAddCircle) := by
  unfold forecastNativeTorusInverse
  rw [forecastNativeFillAxes_restrict, forecastNativeAmbientLinear_mixed U b o R hR w]
  funext a
  rw [ZMod.toAddCircle_intCast, ← AddCircle.coe_add, ← add_div]

theorem forecastNativeCoveredChart_ambient
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ))
    (deck : ∀ j, Q j → ℤ) (a : Σ j, J j) :
    subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
      (normalizedCoveredChart (euclideanSubspace (U a.1)) (b a.1) (hb a.1) (bW a.1) d
        (orthonormalMixedChart (o a.1) (w a.1), integerResidueMap (Q a.1) d (deck a.1)))) a.2 =
      (((normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
        (orthonormalMixedChart (o a.1) (w a.1)) a.2 +
        (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
          (w a.1).2 (deck a.1) a.2 : ℝ)) / d : ℝ) : UnitAddCircle) := by
  rw [normalizedCoveredChart, normalizedCoverLift_add_deck,
    euclideanSubspaceTorusEquiv_mk, subspaceAmbientTorus_mk]
  change (((d : ℝ)⁻¹ * _ : ℝ) : UnitAddCircle) = _
  apply congrArg (fun x : ℝ => (x : UnitAddCircle))
  rw [div_eq_inv_mul]
  congr 1
  exact congrArg (fun v : EuclideanSpace ℝ (J a.1) => v a.2)
    (normalizedDeckPoint_identity (euclideanSubspace (U a.1)) (bW a.1)
      (b a.1) (hb a.1) _ (deck a.1))

omit [Fintype X] in
theorem forecastNative_physical_cover_ambient (d : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j) (u : X → ℝ) (a : Σ j, J j) :
    subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
      (BooleanCubeKernel.physicalSingleSiteValue U d poly hm u a.1 ())) a.2 =
      ((eval u (poly a.1) a.2 / d : ℝ) : UnitAddCircle) := by
  unfold BooleanCubeKernel.physicalSingleSiteValue
  rw [AddEquiv.apply_symm_apply, subspaceAmbientTorus_mk]
  change (((d : ℝ)⁻¹ * ((eval u (restrictCoefficients (U a.1) (poly a.1) (hm a.1))).val a.2) : ℝ) : UnitAddCircle) = _
  rw [eval_restrictCoefficients, div_eq_inv_mul]

namespace NormalizedPolynomialTwist

variable {periodCap coverCap : ℝ} {L : ℝ≥0}

noncomputable def forecastPullback
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (y : Domain) : ℂ := by
  letI : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  exact W.mask residue * W.smooth (forecastNativeSpatialInverse center τ y.1,
    forecastNativeTorusInverse U b o R P W.cover deck frozen y.2)

theorem forecastPullback_norm_le
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ)
    (y : Domain) : ‖W.forecastPullback U b o R P residue deck center τ frozen y‖ ≤ 1 := by
  unfold forecastPullback
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans (W.smooth_bound _)

theorem forecastPullback_lipschitz
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (residue : X → ZMod W.modulus) (deck : (Σ j, J j) → ZMod W.cover)
    (center : X → ℝ) (τ : ℝ) (frozen : {a : LayerSamplerAxis I n // P a} → ℝ) :
    LipschitzWith (L * max ‖τ / 8‖₊ (forecastNativeAmbientLip U b o R))
      (W.forecastPullback U b o R P residue deck center τ frozen) := by
  let : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  have hin := ((forecastNativeSpatialInverse_lipschitz center τ).comp LipschitzWith.prod_fst).prodMk
    ((forecastNativeTorusInverse_lipschitz U b o R P W.cover deck frozen).comp LipschitzWith.prod_snd)
  simp only [mul_one] at hin
  have h := W.smooth_lipschitz.comp hin
  apply LipschitzWith.of_dist_le_mul
  intro y z
  rw [dist_eq_norm]
  change ‖W.mask residue * W.smooth _ - W.mask residue * W.smooth _‖ ≤ _
  rw [← mul_sub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.mask_bound _)).trans
    (by simpa only [Function.comp_apply, dist_eq_norm] using h.dist_le_mul y z)

theorem forecastPullback_mixed
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (hR : ∀ j, R j ≠ 0) (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (β : (Σ j, J j) → ℤ) :
    W.forecastPullback U b o R P (fun x => (u x : ZMod W.modulus))
      (fun a => (β a : ZMod W.cover)) (fun x => (base x : ℝ) / N x) τ
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      W.mask (fun x => (u x : ZMod W.modulus)) *
        W.smooth (fun x => (u x : ℝ) / N x,
          fun a : Σ j, J j => (((normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
            (orthonormalMixedChart (o a.1) (w a.1)) a.2 + β a) / W.cover : ℝ) : UnitAddCircle)) := by
  unfold forecastPullback
  rw [forecastNativeSpatialInverse_integer base u N hN hτ,
    forecastNativeTorusInverse_mixed U b o R P hR]

theorem forecastPullback_covered_mixed
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (hR : ∀ j, R j ≠ 0) (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0)
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Q j → ℤ) :
    let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
    W.forecastPullback U b o R P (fun x => (u x : ZMod W.modulus))
      (fun a => (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
        (w a.1).2 (deck a.1) a.2 : ZMod W.cover)) (fun x => (base x : ℝ) / N x) τ
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      W.mask (fun x => (u x : ZMod W.modulus)) * W.smooth (fun x => (u x : ℝ) / N x,
        fun a : Σ j, J j => subspaceAmbientTorus (U a.1) (euclideanSubspaceTorusEquiv (U a.1)
          (normalizedCoveredChart (euclideanSubspace (U a.1)) (b a.1) (hb a.1) (bW a.1) W.cover
            (orthonormalMixedChart (o a.1) (w a.1), integerResidueMap (Q a.1) W.cover (deck a.1)))) a.2) := by
  intro
  rw [forecastPullback_mixed U b o R P W hR base u N hN hτ]
  simp only [forecastNativeCoveredChart_ambient U b o]

theorem forecastPullback_eval_of_chart
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (hR : ∀ j, R j ≠ 0) (base u : X → ℤ) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ : ℝ} (hτ : τ ≠ 0)
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Basis (Q j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) (deck : ∀ j, Q j → ℤ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    (hchart : let _ : NeZero W.cover := ⟨W.cover_pos.ne'⟩
      ∀ j, BooleanCubeKernel.physicalSingleSiteValue U W.cover poly hm (fun x => (u x : ℝ)) j () =
        normalizedCoveredChart (euclideanSubspace (U j)) (b j) (hb j) (bW j) W.cover
          (orthonormalMixedChart (o j) (w j), integerResidueMap (Q j) W.cover (deck j))) :
    W.forecastPullback U b o R P (fun x => (u x : ZMod W.modulus))
      (fun a => (latticeDeckInteger (euclideanSubspace (U a.1)) (bW a.1) (b a.1) (hb a.1)
        (w a.1).2 (deck a.1) a.2 : ZMod W.cover)) (fun x => (base x : ℝ) / N x) τ
      (fun a => allocatedFullMixedSiteValue (R := R) U b w a.val)
      ((fun a : Spatial => ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8)),
        fun a : Output => allocatedFullMixedSiteValue (R := R) U b w a.1.val) =
      W.eval N poly u := by
  let : NeZero W.cover := ⟨W.cover_pos.ne'⟩
  rw [forecastPullback_covered_mixed U b o R P W hR base u N hN hτ hb bW w deck]
  unfold eval physicalGridFactorInput
  congr 1
  apply congrArg W.smooth
  apply Prod.ext
  · rfl
  funext a
  dsimp only
  rw [← hchart a.1]
  exact forecastNative_physical_cover_ambient U W.cover poly hm _ a

end NormalizedPolynomialTwist
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Classical NNReal BigOperators

variable {X : Type*} [Fintype X] {m : ℕ}
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ) (base : X → ℤ) (N : X → ℕ) (τ : ℝ)

noncomputable def forecastNormalizedAmbientCoordinates
    (p : (X → ℝ) × ((Σ j, J j) → ℝ)) :
    (((Σ _ : X, Unit ⊕ Empty) → ℝ) × (LayerSamplerAxis I n → ℝ)) :=
  (forecastNormalizedSpatialCoordinates base N τ p.1,
    allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered p.2))

theorem forecastNormalizedAmbientCoordinates_lipschitz
    (hR : ∀ j, 0 < R j) (hτ : 0 < τ)
    (C : Fin m → ℝ≥0)
    (hC : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ C j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K) :
    LipschitzWith (max ⟨8 / τ, by positivity⟩ (K * ∑ j, C j * Fintype.card (J j)))
      (forecastNormalizedAmbientCoordinates U b o R base N τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change max (dist (forecastNormalizedSpatialCoordinates base N τ x.1)
    (forecastNormalizedSpatialCoordinates base N τ y.1))
    (dist (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered x.2))
      (allocatedFullAmbientSiteCoordinates (R := R) U b o (singleSiteFromLayered y.2))) ≤ _
  apply max_le
  · have h := (forecastNormalizedSpatialCoordinates_lipschitz base N hτ).dist_le_mul x.1 y.1
    change _ ≤ (8 / τ) * dist x.1 y.1 at h
    exact h.trans ((mul_le_mul_of_nonneg_left (le_max_left (dist x.1 y.1) (dist x.2 y.2))
      (by positivity : 0 ≤ 8 / τ)).trans
      (mul_le_mul_of_nonneg_right (le_max_left (8 / τ)
        ((K * ∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ)) (show (0 : ℝ) ≤ dist x y from dist_nonneg)))
  · have h := (allocatedFullAmbientSiteCoordinates_lipschitz U b o hR C hC K hK).dist_le_mul
        (singleSiteFromLayered x.2) (singleSiteFromLayered y.2)
    have hin : dist (singleSiteFromLayered x.2) (singleSiteFromLayered y.2) ≤ dist x y :=
      (singleSiteFromLayered_lipschitz.dist_le_mul x.2 y.2 |>.trans_eq (one_mul _)).trans
        (le_max_right (dist x.1 y.1) (dist x.2 y.2))
    exact h.trans ((mul_le_mul_of_nonneg_left hin (NNReal.coe_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (le_max_right (8 / τ)
        ((K * ∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ)) (show (0 : ℝ) ≤ dist x y from dist_nonneg)))

omit [Fintype X] in
theorem forecastNormalizedAmbientCoordinates_mixed (u : X → ℤ)
    (w : ∀ j, (I j → ℝ) × (Fin (n j) → ℤ)) :
    forecastNormalizedAmbientCoordinates U b o R base N τ
      (fun i => (u i : ℝ) / N i,
        fun a => normalizedLatticePoint (euclideanSubspace (U a.1)) (b a.1)
          (orthonormalMixedChart (o a.1) (w a.1)) a.2) =
      (fun a : Σ _ : X, Unit ⊕ Empty =>
        ((u a.1 : ℝ) - base a.1) / (τ * N a.1 / 8),
        allocatedFullMixedSiteValue (R := R) U b w) := by
  apply Prod.ext
  · funext a
    exact forecastNormalizedSpatialCoordinates_eval base u N τ a
  · exact allocatedFullAmbientSiteCoordinates_layered_point U b o w

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X Zsp : Type*} [Fintype G] [Fintype X]
  [Fintype Zsp] [DecidableEq Zsp]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Sample" => CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
local notation "Output" => (Σ _a : Active, Unit)
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Domain" => ((Spatial → ℝ) × (Output → ℝ))
local notation "noise" => allocatedSampleRestrictedProfileNoise B U basis S short
local notation "hamin" => unitProfilePrincipalLowerBound_pos B

variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
  {δ : ℝ} (hδ : 0 < δ)
  (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)

local notation "density" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width
include hR hσ hδ hw hl in

theorem allocatedOriginalSampleForecastDensity_supported_zero_off_ball
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Domain) (hy : 3 < ‖y‖) : density sample y = 0 := by
  exact allocatedFixedPathForecastDensity_zero_off_ball (X := X)
    B short R σ s root D hp hW hL (fun j => (hR j).ne') hB lower width
    hamin hδ (fun a => unitProfilePrincipalLowerBound_le B a.val) hw hl (noise sample)
    (allocatedSampleRestrictedProfileNoise_short_abs_le B U basis hR hσ S sample hs)
    hroot hwidth y hy

include hR hσ hδ hw hl in

theorem allocatedOriginalSampleForecastDensity_nonzero_active_bounds
    (sample : Sample)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hroot : (∑ j, |(root j : ℝ)|) ≤ W)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (y : Spatial → ℝ) (v : LayerSamplerAxis I n → ℝ)
    (hnonzero : density sample (y, forecastNormalizedActiveCoordinates short v) ≠ 0) :
    ∀ a : {a : LayerSamplerAxis I n // ¬short a}, |v a.val| ≤ 3 := by
  have hnorm : ‖(y, forecastNormalizedActiveCoordinates short v)‖ ≤ 3 := by
    apply le_of_not_gt
    intro h
    exact hnonzero (allocatedOriginalSampleForecastDensity_supported_zero_off_ball (X := X)
      B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl
      sample hs hroot hwidth _ h)
  change max ‖y‖ ‖forecastNormalizedActiveCoordinates short v‖ ≤ 3 at hnorm
  have hactive : ‖forecastNormalizedActiveCoordinates short v‖ ≤ 3 :=
    (le_max_right _ _).trans hnorm
  intro a
  have h := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)).mp hactive ⟨a, ()⟩
  simpa only [forecastNormalizedActiveCoordinates, Real.norm_eq_abs] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (R : Fin m → ℝ)

def forecastNativePrimitiveBudget (basisBound radiusBound : Fin m → ℝ≥0) : ℝ≥0 :=
  ∑ j, (1 + (n j : ℝ≥0) * (basisBound j + 1)) *
    (Fintype.card (I j) + 1) * radiusBound j

theorem forecastNativeAmbientLip_le_basis_bound
    (basisBound radiusBound : Fin m → ℝ≥0)
    (hb : ∀ j i, ‖b j i‖ ≤ basisBound j) (hR : ∀ j, ‖R j‖ ≤ radiusBound j) :
    forecastNativeAmbientLip U b o R ≤
      forecastNativePrimitiveBudget (I := I) (n := n) basisBound radiusBound := by
  change ‖(forecastNativeAmbientLinear U b o R).toContinuousLinearMap‖ ≤
    (forecastNativePrimitiveBudget (I := I) (n := n) basisBound radiusBound : ℝ)
  apply (forecastNativeAmbientLinear U b o R).toContinuousLinearMap.opNorm_le_bound
    (NNReal.coe_nonneg _)
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))).mpr
  intro a
  have hcoord (k : LayerSamplerAxis I n) :
      |R a.1 * v k| ≤ (radiusBound a.1 : ℝ) * ‖v‖ := by
    rw [← Real.norm_eq_abs, norm_mul]
    exact mul_le_mul (hR a.1) (norm_le_pi_norm v k) (norm_nonneg _) (NNReal.coe_nonneg _)
  have hrow := mixedRealPoint_norm_le (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    (show (0 : ℝ) ≤ 1 + (n a.1 : ℝ) * ((basisBound a.1 : ℝ) + 1) by positivity)
    (mul_nonneg (NNReal.coe_nonneg (radiusBound a.1)) (norm_nonneg v))
    (normalizedOrthogonalChart_symm_norm_le (euclideanSubspace (U a.1)) (b a.1)
      (NNReal.coe_nonneg _) (hb a.1))
    (fun i => R a.1 * v ⟨a.1, Sum.inl i⟩)
    (fun i => R a.1 * v ⟨a.1, Sum.inr i⟩)
    (fun i => hcoord ⟨a.1, Sum.inl i⟩) (fun i => hcoord ⟨a.1, Sum.inr i⟩)
  have hsum :
      (1 + (n a.1 : ℝ≥0) * (basisBound a.1 + 1)) *
        (Fintype.card (I a.1) + 1) * radiusBound a.1 ≤
      forecastNativePrimitiveBudget (I := I) (n := n) basisBound radiusBound :=
    Finset.single_le_sum
      (f := fun j => (1 + (n j : ℝ≥0) * (basisBound j + 1)) *
        (Fintype.card (I j) + 1) * radiusBound j)
      (fun _ _ => zero_le) (Finset.mem_univ a.1)
  have hpoint := (PiLp.norm_apply_le (mixedRealPoint (euclideanSubspace (U a.1))
    (b a.1) (o a.1) ((fun i => R a.1 * v ⟨a.1, Sum.inl i⟩),
      fun i => R a.1 * v ⟨a.1, Sum.inr i⟩)) a.2).trans hrow
  change ‖mixedRealPoint (euclideanSubspace (U a.1)) (b a.1) (o a.1)
    ((fun i => R a.1 * v ⟨a.1, Sum.inl i⟩),
      fun i => R a.1 * v ⟨a.1, Sum.inr i⟩) a.2‖ ≤ _
  apply hpoint.trans
  convert mul_le_mul_of_nonneg_right (show
    (((1 + (n a.1 : ℝ≥0) * (basisBound a.1 + 1)) *
      (Fintype.card (I a.1) + 1) * radiusBound a.1 : ℝ≥0) : ℝ) ≤
        (forecastNativePrimitiveBudget (I := I) (n := n) basisBound radiusBound : ℝ)
    from hsum) (norm_nonneg v) using 1
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_one, NNReal.coe_natCast]
  ring

theorem forecastNativeAmbientLip_le_explicit :
    forecastNativeAmbientLip U b o R ≤
      forecastNativePrimitiveBudget (I := I) (n := n)
        (fun j => ∑ i, ‖b j i‖₊) (fun j => ‖R j‖₊) := by
  apply forecastNativeAmbientLip_le_basis_bound
  · intro j i
    exact_mod_cast (Finset.single_le_sum (f := fun i => ‖b j i‖₊)
      (fun _ _ => zero_le) (Finset.mem_univ i))
  · intro j
    exact le_rfl

theorem forecastNativeAmbientLip_le_polynomial {p : ℝ≥0}
    (hm : (m : ℝ≥0) ≤ p) (hn : ∀ j, (n j : ℝ≥0) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ≥0) ≤ p)
    (hb : ∀ j i, ‖b j i‖ ≤ p) (hR : ∀ j, ‖R j‖ ≤ 1) :
    forecastNativeAmbientLip U b o R ≤ (p + 1) ^ 4 := by
  apply (forecastNativeAmbientLip_le_basis_bound U b o R (fun _ => p) (fun _ => 1) hb hR).trans
  have hfactor : 1 + p * (p + 1) ≤ (p + 1) ^ 2 := by nlinarith
  calc
    forecastNativePrimitiveBudget (I := I) (n := n) (fun _ => p) (fun _ => 1)
        ≤ ∑ _j : Fin m, (p + 1) ^ 3 := by
      apply Finset.sum_le_sum
      intro j _
      simp only [mul_one]
      calc
        (1 + (n j : ℝ≥0) * (p + 1)) * (Fintype.card (I j) + 1)
            ≤ (1 + p * (p + 1)) * (p + 1) := by gcongr <;> first | exact hn j | exact hI j
        _ ≤ (p + 1) ^ 2 * (p + 1) := mul_le_mul' hfactor le_rfl
        _ = (p + 1) ^ 3 := by ring
    _ = (m : ℝ≥0) * (p + 1) ^ 3 := by simp
    _ ≤ (p + 1) * (p + 1) ^ 3 := mul_le_mul' (hm.trans (le_add_of_nonneg_right zero_le_one)) le_rfl
    _ = (p + 1) ^ 4 := by ring

theorem forecastNativeAmbientLip_le_exp {p : ℝ} (hp : 0 ≤ p)
    (hm : (m : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p)
    (hb : ∀ j i, ‖b j i‖ ≤ Real.exp p) (hR : ∀ j, ‖R j‖ ≤ 1) :
    (forecastNativeAmbientLip U b o R : ℝ) ≤ Real.exp (4 * (p + 1)) := by
  have he : p ≤ Real.exp p := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp p)
  have hexp : (Real.toNNReal (Real.exp p) : ℝ) = Real.exp p :=
    Real.coe_toNNReal _ (Real.exp_pos p).le
  have hbound := forecastNativeAmbientLip_le_polynomial U b o R
    (p := Real.toNNReal (Real.exp p))
    (by change (m : ℝ) ≤ (Real.toNNReal (Real.exp p) : ℝ); rw [hexp]; exact hm.trans he)
    (fun j => by change (n j : ℝ) ≤ (Real.toNNReal (Real.exp p) : ℝ); rw [hexp]; exact (hn j).trans he)
    (fun j => by change (Fintype.card (I j) : ℝ) ≤ (Real.toNNReal (Real.exp p) : ℝ); rw [hexp]; exact (hI j).trans he)
    (fun j i => by simpa only [hexp] using hb j i) hR
  have hboundR : (forecastNativeAmbientLip U b o R : ℝ) ≤ (Real.exp p + 1) ^ 4 := by
    have hr : (forecastNativeAmbientLip U b o R : ℝ) ≤
        (((Real.toNNReal (Real.exp p) + 1) ^ 4 : ℝ≥0) : ℝ) := hbound
    simpa only [NNReal.coe_pow, NNReal.coe_add, NNReal.coe_one, hexp] using hr
  have he1 : 2 ≤ Real.exp (1 : ℝ) := by simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
  have hp1 : 1 ≤ Real.exp p := Real.one_le_exp_iff.mpr hp
  have hplus : Real.exp p + 1 ≤ Real.exp (p + 1) := by
    rw [Real.exp_add]
    nlinarith
  calc
    _ ≤ (Real.exp p + 1) ^ 4 := hboundR
    _ ≤ (Real.exp (p + 1)) ^ 4 := pow_le_pow_left₀ (by positivity) hplus _
    _ = Real.exp (4 * (p + 1)) := by rw [← Real.exp_nat_mul]; norm_num

end Erdos3.VectorPolynomial

end

end OAI
