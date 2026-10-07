import OAI.Combinatorics.Progressions.Geometry.AllocatedNarrowSpatialCanonicalComparison

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical NNReal
variable {G X : Type*} [Fintype G] [Fintype X]

noncomputable def fixedSpatialKernelMap (W L : ℝ) (z : Option G × X → ℝ)
    (t : G → ℝ) : (Σ _ : X, Unit ⊕ Empty) → ℝ :=
  fun a => z (none, a.1) + (L / (1 + W)) * ∑ g, z (some g, a.1) * t g

theorem fixedSpatialKernelMap_lipschitz (W L : ℝ) (z : Option G × X → ℝ)
    (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith ((Fintype.card G : ℝ≥0) * ‖L / (1 + W)‖₊)
      (fixedSpatialKernelMap W L z) := by
  apply LipschitzWith.of_dist_le_mul
  intro t u
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) dist_nonneg)).mpr
  intro a
  change |(z (none, a.1) + _ * _) - (z (none, a.1) + _ * _)| ≤ _
  rw [add_sub_add_left_eq_sub, ← mul_sub, abs_mul]
  have hsum : |(∑ g, z (some g, a.1) * t g) - ∑ g, z (some g, a.1) * u g| ≤
      (Fintype.card G : ℝ) * dist t u := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ g, |z (some g, a.1) * t g - z (some g, a.1) * u g| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _g : G, dist t u := by
        apply Finset.sum_le_sum
        intro g _
        rw [← mul_sub, abs_mul]
        exact (mul_le_mul_of_nonneg_right (hz g a.1) (abs_nonneg _)).trans
          (by simpa only [one_mul, Real.dist_eq] using dist_le_pi_dist t u g)
      _ = _ := by simp
  have h := mul_le_mul_of_nonneg_left hsum (abs_nonneg (L / (1 + W)))
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, coe_nnnorm, Real.norm_eq_abs,
    mul_left_comm, mul_assoc] using h

theorem fixedSpatialKernelMap_lipschitz_one {W L : ℝ}
    (hW : 0 ≤ W) (hL : 0 ≤ L) (hsize : (Fintype.card G : ℝ) * L ≤ W)
    (z : Option G × X → ℝ) (hz : ∀ g x, |z (some g, x)| ≤ 1) :
    LipschitzWith 1 (fixedSpatialKernelMap W L z) := by
  apply (fixedSpatialKernelMap_lipschitz W L z hz).weaken
  change (Fintype.card G : ℝ) * ‖L / (1 + W)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hL (by linarith))]
  rw [← mul_div_assoc]
  exact (div_le_one (by linarith : 0 < 1 + W)).mpr (by linarith)

variable [DecidableEq G]

omit [Fintype X] in
theorem fixedSpatialKernelMap_integer (s : Empty ↪ G) (root : G → ℤ)
    (D : Matrix Empty G ℤ) {W L : ℝ} (hW : 0 ≤ W) (hL : L ≠ 0)
    (z : Option G × X → ℝ) :
    fixedSpatialKernelMap W L z (fun g => (root g : ℝ) / L) =
      canonicalZeroSpatialInputMap s root D W L z := by
  funext a
  rcases a with ⟨x, a⟩
  cases a with
  | inr e => exact Empty.elim e
  | inl u =>
    cases u
    rw [canonicalZeroSpatialInputMap_apply s root D W L hW]
    unfold fixedSpatialKernelMap
    simp only
    congr 1
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro g _
    field_simp

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical
variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

noncomputable def fixedSpatialKernelBlock (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (second : Bool) : Matrix X X ℝ :=
  fun x i => (L / (1 + W)) * z (some (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)), x)

noncomputable def fixedSpatialKernelRest (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (t : T → ℝ) : X → ℝ :=
  fun x => (L / (1 + W)) * ∑ j, z (some (e.symm (Sum.inr (Sum.inr j))), x) * t j

omit [Fintype G] [Fintype X] in
theorem fixedSpatialKernelRest_measurable (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) :
    Measurable (fixedSpatialKernelRest e W L z) := by
  unfold fixedSpatialKernelRest
  fun_prop

theorem fixedSpatialKernelMap_blocks (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ)
    (u v : X → ℝ) (t : T → ℝ) (x : X) :
    fixedSpatialKernelMap W L z ((Sum.elim u (Sum.elim v t)) ∘ e) ⟨x, Sum.inl ()⟩ =
      z (none, x) + (fixedSpatialKernelBlock e W L z false).mulVec u x +
        (fixedSpatialKernelBlock e W L z true).mulVec v x +
        fixedSpatialKernelRest e W L z t x := by
  unfold fixedSpatialKernelMap
  rw [← e.symm.sum_comp]
  simp only [Function.comp_apply, Equiv.apply_symm_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  unfold fixedSpatialKernelBlock fixedSpatialKernelRest Matrix.mulVec dotProduct
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.mul_sum]
  simp only [mul_add, Finset.mul_sum, mul_assoc]
  ring

theorem fixedSpatialKernelMap_blocks_actual (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ) (t : G → ℝ) (x : X) :
    fixedSpatialKernelMap W L z t ⟨x, Sum.inl ()⟩ =
      z (none, x) + (fixedSpatialKernelBlock e W L z false).mulVec
          (fun i => t (e.symm (Sum.inl i))) x +
        (fixedSpatialKernelBlock e W L z true).mulVec
          (fun i => t (e.symm (Sum.inr (Sum.inl i)))) x +
        fixedSpatialKernelRest e W L z (fun j => t (e.symm (Sum.inr (Sum.inr j)))) x := by
  convert fixedSpatialKernelMap_blocks e W L z
    (fun i => t (e.symm (Sum.inl i))) (fun i => t (e.symm (Sum.inr (Sum.inl i))))
    (fun j => t (e.symm (Sum.inr (Sum.inr j)))) x using 1
  congr 1
  funext g
  simp only [Function.comp_apply]
  generalize he : e g = a
  have hg := congrArg e.symm he
  simp only [Equiv.symm_apply_apply] at hg
  subst g
  rcases a with i | (i | j) <;> rfl

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem rectangularWeightIndices_normalized_norm_le
    {K : Type*} [Fintype K] (V : K → ℝ) (hV : ∀ k, 0 < V k)
    {z : K → ℤ} (hz : z ∈ rectangularWeightIndices 0 V 1) :
    ‖fun k => (z k : ℝ) / V k‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro k
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hV k), div_le_one (hV k)]
  exact rectangularWeightIndices_zero_bound V hz k

theorem selectedResidueSmoothPMF_normalized_norm_le
    {K X : Type*} [Fintype K] [Fintype X]
    (modulus : X → ℕ) (cells : Finset (ColumnResiduePattern K X modulus))
    (V : K × X → ℝ) (hV : ∀ k, 0 < V k)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus cells V z)
    {z : K × X → ℤ} (hz : z ∈ (selectedResidueSmoothPMF modulus cells V hV hZ).support) :
    ‖fun k => (z k : ℝ) / V k‖ ≤ 1 := by
  apply rectangularWeightIndices_normalized_norm_le V hV
  by_contra hn
  have hpos := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hz) (PMF.apply_ne_top _ _)
  have hzero : (selectedResidueSmoothPMF modulus cells V hV hZ z).toReal = 0 := by
    rw [selectedResidueSmoothPMF_toReal,
      selectedResidueSmoothWeight_zero_off modulus cells V hV z hn, zero_div]
  exact hpos.ne' hzero

variable {G N X : Type*} [Fintype G] [DecidableEq G]
  [Fintype N] [DecidableEq N] [Fintype X]

theorem fixedSpatialKernelMap_narrow_physical_dist
    (root : G → ℤ) (principal : N → ℤ) {W L τ ξ : ℝ}
    (hW : 0 ≤ W) (hL : L ≠ 0) (hξ : 0 < ξ)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W)
    (box : X → ℕ) (z : Option (G ⊕ N) × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k‖ ≤ 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap W L
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G N X)
        (fun g => (root g : ℝ) / L)) ≤ ξ := by
  let s : Empty ↪ G := ⟨Empty.elim, fun e => Empty.elim e⟩
  let sf : Empty ↪ (G ⊕ N) := ⟨Empty.elim, fun e => Empty.elim e⟩
  let D : Matrix Empty G ℤ := fun e => Empty.elim e
  let Df : Matrix Empty (G ⊕ N) ℤ := fun e => Empty.elim e
  have hsite : canonicalZeroSpatialInputMap sf (Sum.elim root principal) Df W L
      (canonicalZeroSpatialNarrowInput ξ
        (fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k)) =
      fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8) := by
    funext o
    rcases o with ⟨x, a⟩
    cases a with
    | inr e => exact Empty.elim e
    | inl a =>
      cases a
      exact canonicalZeroSpatialNarrowInputMap_physicalSite sf _ Df hW hξ.ne' L τ box z x
  rw [fixedSpatialKernelMap_integer s root D hW hL, ← hsite, dist_eq_norm]
  exact (canonicalZeroSpatialNarrowPrincipal_norm_le s sf root principal D Df W L
    hW ξ hξ.le _ hz).trans (mul_le_of_le_one_right hξ.le
      (canonicalZeroSpatialPrincipal_mass_ratio_le_one root principal W hW hbudget))

theorem fixedSpatialKernelMap_narrow_physical_test_error
    (root : G → ℤ) (principal : N → ℤ) {W L τ ξ : ℝ}
    (hW : 0 ≤ W) (hL : L ≠ 0) (hξ : 0 < ξ)
    (hbudget : (∑ k : G ⊕ N, |((Sum.elim root principal k : ℤ) : ℝ)|) ≤ W)
    (box : X → ℕ) (z : Option (G ⊕ N) × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k‖ ≤ 1)
    {A : ℝ≥0} (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    (hφ : LipschitzWith A φ) :
    ‖φ (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (Sum.elim root principal) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8)) -
      φ (fixedSpatialKernelMap W L
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths W τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G N X)
        (fun g => (root g : ℝ) / L))‖ ≤ (A : ℝ) * ξ := by
  rw [← dist_eq_norm]
  exact (hφ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
    (fixedSpatialKernelMap_narrow_physical_dist root principal hW hL hξ hbudget box z hz)
    A.coe_nonneg)

namespace VectorPolynomial

variable {m : ℕ} {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedFixedSpatialKernelMap_narrow_physical_dist
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hξ : 0 < ξ) (box : X → ℕ)
    (z : Option vars × X → ℤ)
    (hz : ‖fun k => (z k : ℝ) /
      narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box k‖ ≤ 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ))) ≤ ξ := by
  have hr : allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y =
      Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) := by
    funext k
    simp only [allocatedPhysicalCubeRoot, zero_add]
  have hbudget : (∑ k : vars,
      |((Sum.elim (fun g => (x g none : ℤ)) (fun j => (y j none : ℤ)) k : ℤ) : ℝ)|) ≤ budget := by
    simpa only [hr] using allocatedPhysicalCube_root_sum B U basis S (fun _ => 0) x y
  rw [hr]
  exact fixedSpatialKernelMap_narrow_physical_dist _ _
    (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0))
    (Nat.cast_ne_zero.mpr S.positive.ne') hξ hbudget box z hz

theorem allocatedFixedSpatialKernelMap_supported_narrow_physical_dist
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (z : Option vars × X → ℤ)
    (hz : z ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ))) ≤ ξ := by
  exact allocatedFixedSpatialKernelMap_narrow_physical_dist B U basis S x y hξ box z
    (rectangularWeightIndices_normalized_norm_le _
      (narrowTrimmedSpatialWidths_pos
        (allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)) hτ hξ box hbox) hz)

theorem allocatedFixedSpatialKernelMap_supported_narrow_physical_test_error
    (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (z : Option vars × X → ℤ)
    (hz : z ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1)
    {A : ℝ≥0} (φ : ((Σ _ : X, Unit ⊕ Empty) → ℝ) → ℂ)
    (hφ : LipschitzWith A φ) :
    ‖φ (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) z o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8)) -
      φ (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (z k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((x g none : ℤ) : ℝ) / (S.value : ℝ)))‖ ≤ (A : ℝ) * ξ := by
  rw [← dist_eq_norm]
  exact (hφ.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left
    (allocatedFixedSpatialKernelMap_supported_narrow_physical_dist
      B U basis S x y hτ hξ box hbox z hz) A.coe_nonneg)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {G X T : Type*} [Fintype G] [Fintype X] [Fintype T]

def fixedSpatialKernelBlockCoordinates (e : G ≃ X ⊕ (X ⊕ T))
    (t : G → ℝ) : (T → ℝ) × ((X → ℝ) × (X → ℝ)) :=
  (fun j => t (e.symm (.inr (.inr j))),
    (fun i => t (e.symm (.inl i)), fun i => t (e.symm (.inr (.inl i)))))

theorem fixedSpatialKernelBlockCoordinates_measurePreserving (e : G ≃ X ⊕ (X ⊕ T)) :
    MeasurePreserving (fixedSpatialKernelBlockCoordinates e) (unitBoxMeasure G)
      ((unitBoxMeasure T).prod ((unitBoxMeasure X).prod (unitBoxMeasure X))) := by
  let e' := e.trans (Equiv.sumAssoc X X T).symm
  have hr := (unitBoxMeasure_sum (X ⊕ X) T).comp (unitBoxMeasure_reindex e')
  have hp := ((unitBoxMeasure_sum X X).prod (MeasurePreserving.id (unitBoxMeasure T))).comp hr
  have hs := (Measure.measurePreserving_swap
    (μ := (unitBoxMeasure X).prod (unitBoxMeasure X)) (ν := unitBoxMeasure T)).comp hp
  convert hs using 1
  funext t
  ext j <;> simp [fixedSpatialKernelBlockCoordinates, e',
    MeasurableEquiv.coe_piCongrLeft, MeasurableEquiv.coe_sumPiEquivProdPi,
    Equiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply_eq_cast]

theorem fixedSpatialKernelBlockCoordinates_image_law (e : G ≃ X ⊕ (X ⊕ T)) :
    (unitBoxMeasure G).map (fixedSpatialKernelBlockCoordinates e) =
      (unitBoxMeasure T).prod ((unitBoxMeasure X).prod (unitBoxMeasure X)) :=
  (fixedSpatialKernelBlockCoordinates_measurePreserving e).map_eq

variable [DecidableEq X]

theorem fixedSpatialKernelMap_block_image_law (e : G ≃ X ⊕ (X ⊕ T))
    (W L : ℝ) (z : Option G × X → ℝ)
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ))
    (hA : ∀ u, A u = (fixedSpatialKernelBlock e W L z false).mulVec u)
    (hB : ∀ u, B u = (fixedSpatialKernelBlock e W L z true).mulVec u) :
    (unitBoxMeasure G).map (fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩) =
      realDensityMeasure volume (fixedSpatialBlockDensity (unitBoxMeasure T)
        (fun x => z (none, x)) (fixedSpatialKernelRest e W L z) A B) := by
  have h := fixedSpatialBlockDensity_image_law (unitBoxMeasure T) (fun x => z (none, x))
    (fixedSpatialKernelRest_measurable e W L z) A B
  let F := fun p : (T → ℝ) × ((X → ℝ) × (X → ℝ)) =>
    (fun x => z (none, x)) + A p.2.1 + B p.2.2 + fixedSpatialKernelRest e W L z p.1
  have hF : Measurable F := by
    exact ((measurable_const.add (A.continuous.measurable.comp (measurable_fst.comp measurable_snd))).add
      (B.continuous.measurable.comp (measurable_snd.comp measurable_snd))).add
      ((fixedSpatialKernelRest_measurable e W L z).comp measurable_fst)
  change ((unitBoxMeasure T).prod ((unitBoxMeasure X).prod (unitBoxMeasure X))).map F = _ at h
  rw [← fixedSpatialKernelBlockCoordinates_image_law e,
    Measure.map_map hF (fixedSpatialKernelBlockCoordinates_measurePreserving e).measurable] at h
  have he : F ∘ fixedSpatialKernelBlockCoordinates e =
      fun t x => fixedSpatialKernelMap W L z t ⟨x, .inl ()⟩ := by
    funext t x
    simp only [Function.comp_apply, F, fixedSpatialKernelBlockCoordinates, Pi.add_apply, hA, hB]
    exact (fixedSpatialKernelMap_blocks_actual e W L z t x).symm
  rw [he] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]

noncomputable def fixedSpatialKernelSliceFrame (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) : Option G × X → ℝ :=
  fun a => match a.1 with
    | none => z (none, a.2) + (L / (1 + W)) * ∑ g, z (some g, a.2) * lower g
    | some g => width g * z (some g, a.2)

@[simp] theorem fixedSpatialKernelSliceFrame_none (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (x : X) :
    fixedSpatialKernelSliceFrame W L z lower width (none, x) =
      z (none, x) + (L / (1 + W)) * ∑ g, z (some g, x) * lower g := rfl

@[simp] theorem fixedSpatialKernelSliceFrame_some (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (g : G) (x : X) :
    fixedSpatialKernelSliceFrame W L z lower width (some g, x) =
      width g * z (some g, x) := rfl

theorem fixedSpatialKernelMap_slice (W L : ℝ)
    (z : Option G × X → ℝ) (lower width t : G → ℝ) :
    fixedSpatialKernelMap W L (fixedSpatialKernelSliceFrame W L z lower width) t =
      fixedSpatialKernelMap W L z (fun g => lower g + width g * t g) := by
  funext a
  simp only [fixedSpatialKernelMap, fixedSpatialKernelSliceFrame_none,
    fixedSpatialKernelSliceFrame_some, mul_add, Finset.sum_add_distrib,
    mul_assoc, mul_left_comm]
  ring

variable {T : Type*} [Fintype X]

omit [Fintype X] in
theorem fixedSpatialKernelBlock_slice (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool) :
    fixedSpatialKernelBlock e W L (fixedSpatialKernelSliceFrame W L z lower width) second =
      fun x i => fixedSpatialKernelBlock e W L z second x i *
        width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
  funext x i
  simp only [fixedSpatialKernelBlock, fixedSpatialKernelSliceFrame_some]
  ring

theorem fixedSpatialKernelBlock_slice_det (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool) :
    (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det =
      (fixedSpatialKernelBlock e W L z second).det *
        ∏ i, width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i)) := by
  have hmatrix : fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second =
      fixedSpatialKernelBlock e W L z second * Matrix.diagonal
        (fun i => width (e.symm (if second then Sum.inr (Sum.inl i) else Sum.inl i))) := by
    ext x i
    simp only [Matrix.mul_diagonal, fixedSpatialKernelBlock, fixedSpatialKernelSliceFrame_some]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_diagonal]

theorem fixedSpatialKernelBlock_slice_det_ne_zero
    (e : G ≃ X ⊕ (X ⊕ T)) (W L : ℝ)
    (z : Option G × X → ℝ) (lower width : G → ℝ) (second : Bool)
    (hdet : (fixedSpatialKernelBlock e W L z second).det ≠ 0)
    (hwidth : ∀ g, width g ≠ 0) :
    (fixedSpatialKernelBlock e W L
      (fixedSpatialKernelSliceFrame W L z lower width) second).det ≠ 0 := by
  rw [fixedSpatialKernelBlock_slice_det]
  exact mul_ne_zero hdet (Finset.prod_ne_zero_iff.mpr (fun _ _ => hwidth _))

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {G : Type*} [Fintype G]

noncomputable def containedKernelCubeMap (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g)) : G → IntegerScalarCubeBox Empty S :=
  fun g => containedProgressionCubeMap Empty S (H g) (step g) (c g) hS (hsubset g) (x g)

theorem containedKernelCubeMap_value (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (g : G) :
    (containedKernelCubeMap S H step c hS hsubset x g none : ℤ) =
      c g + (step g : ℤ) * (x g none : ℤ) := by
  have hpos := lt_of_le_of_ne ((FiniteProbabilityWeights.pi
    (fun g => integerScalarCubeWeights Empty (H g) (hH g))).nonneg x) hx.symm
  have hg := FiniteProbabilityWeights.pi_weight_pos_component
    (fun g => integerScalarCubeWeights Empty (H g) (hH g)) x hpos g
  have hcube := (mem_integerScalarCubeSet (H g) (x g)).mp
    ((FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ (x g)).mp hg).1
  simpa only [containedKernelCubeMap, ite_true] using
    (containedProgressionCubeMap_value Empty S (H g) (step g) (c g) hS
      (hsubset g) (x g) hcube none)

theorem containedKernelCubeMap_normalized (S : ℕ) (H step : G → ℕ) (c : G → ℤ)
    (hS : 0 < S) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0) :
    (fun g => ((containedKernelCubeMap S H step c hS hsubset x g none : ℤ) : ℝ) / S) =
      fun g => ((c g : ℝ) + (step g : ℝ) * (x g none : ℝ)) / S := by
  funext g
  rw [containedKernelCubeMap_value S H step c hS hH hsubset x hx g]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]

namespace VectorPolynomial

variable {m : ℕ} {X : Type*} [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "principal" => PrincipalTupleIndex B (layerSamplerDegree I n)
local notation "vars" => LayerSamplerVariables G I n B
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)

theorem allocatedContainedKernel_supported_narrow_physical_dist
    (H step : G → ℕ) (c : G → ℤ) (hH : ∀ g, 0 < H g)
    (hsubset : ∀ g, integerProgressionSupport (c g) (step g : ℤ) (H g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ))
    (x : ∀ g, IntegerScalarCubeBox Empty (H g))
    (hx : (FiniteProbabilityWeights.pi
      (fun g => integerScalarCubeWeights Empty (H g) (hH g))).weight x ≠ 0)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty (allocatedPrincipalSides B U basis S))
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ) (box : X → ℕ) (hbox : ∀ o, 0 < box o)
    (integerFrame : Option vars × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := principal) budget τ ξ box) 1) :
    dist (fun o : Σ _ : X, Unit ⊕ Empty =>
        (integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
          (containedKernelCubeMap S.value H step c S.positive hsubset x) y) integerFrame o.1 : ℝ) /
          (τ * (box o.1 : ℝ) / 8))
      (fixedSpatialKernelMap budget (S.value : ℝ)
        ((fun k => (integerFrame k : ℝ) / narrowTrimmedSpatialWidths budget τ ξ box k) ∘
          canonicalZeroSpatialKernelEmbedding G principal X)
        (fun g => ((c g : ℝ) + (step g : ℝ) * (x g none : ℝ)) / S.value)) ≤ ξ := by
  rw [← containedKernelCubeMap_normalized S.value H step c S.positive hH hsubset x hx]
  exact allocatedFixedSpatialKernelMap_supported_narrow_physical_dist B U basis S
    (containedKernelCubeMap S.value H step c S.positive hsubset x) y
    hτ hξ box hbox integerFrame hframe

end VectorPolynomial
end Erdos3

end

end OAI
