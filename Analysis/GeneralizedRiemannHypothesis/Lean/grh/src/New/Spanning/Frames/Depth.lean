import New.Spanning.Frames.QuadricPlancherel

/-!
# Depth

For a fixed position few frame vectors are deep, and for a fixed frame vector few translates of the
position leave it shallow. Both are read on vectors that look the same from the two points. A
position far from 1 has a deep vector, and a head keeps the first vectors shallow. The letters
G^(l), R^(l), U_(<l), Y^(l) are those of the head of `New.Spanning.Frames.Lengths`, and K, M those
of `New.Spanning.Frames.Levels`.

## Main definitions and results

* `New.Floors.PlaceData.IsCommonBound.depth_le`, `New.Floors.Gauge.floorMassLe_depth_pow`,
  `New.Floors.Gauge.lintegral_depth_pow_section_le`: deep vectors are rare, also on a section.
* `New.Floors.Gauge.exists_lift_of_mem_closeBelow`,
  `New.Floors.Gauge.lintegral_heisenbergMeasure_inv_depth_le`: long coordinates force depth.
* `New.Floors.Gauge.lintegral_invDepthWeight_le`, `New.Floors.Gauge.lintegral_depthWeight_le`: the
  two halves of the weight over all floors of a head.
* `New.Floors.Gauge.hasMatrixSize_sub_one_of_stableProducts`,
  `New.Floors.Gauge.exists_unit_mem_stableProducts_of_isHead`: bounded depths bound the position;
  under a head, each 𝔡_a with a < j contains a unit with bounded inverse.

Notions from other files:
* `F.IsStable l g g' ω`: ω is orthogonal to the e_b, b < l, and (g⁻¹ ω, g'⁻¹ ω') lies in
  `F.closePairs` for some ω' congruent to ω modulo these e_b.
* `F.stableProducts a x y`: the set 𝔡_a of the products ⟨e_a, ω⟩ with the ω stable at x and x y.
* `F.depth a x y`: the inverse of the volume of 𝔡_a.
* `F.depthWeight j x y`: the product over a < j of the depth^(-s), s = `F.volumeExponent`.
* `F.IsNear j g`: ξ g lies in the box `F.boxSet` for some ξ in `partialUnitriangularGroup j`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Set Function FloorGroups Size Place TraceOne PlaceData
  HyperbolicBasis Finset

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Place A] [Fintype ι] [DecidableEq ι] {m j : ℕ} {a : Fin 𝔰.ϱ} {T : 𝔰.Form A}
  [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {g x y σ ξ : T.G}

namespace PlaceData

/-- A vector ω orthogonal to the e_b, b < l, and short from the points g and g' (the pair
(g⁻¹ ω, g'⁻¹ ω) is close) is stable at g and g', with the same lift at both points. -/
lemma IsShortFrom.isStable {l : ℕ} {g' : T.G} {ω : 𝔰.BesselIndex → A} (h : F.IsShortFrom g g' ω)
    (h_orth : IsOrthogonalBelow l ω) : F.IsStable l g g' ω :=
  ⟨h_orth, ω, .refl l ω, h⟩

/-- The sets 𝔡_a = `F.stableProducts a x y` form an open family in (x, y). -/
lemma isOpen_setOf_mem_stableProducts : IsOpen
  {((x, y), c) : (T.G × T.G) × A | c ∈ F.stableProducts a x y} := by
  refine isOpen_iff_eventually.2 ?_
  rintro ⟨⟨x, y⟩, c⟩ ⟨w, ⟨h_orth, w', h_congr, h_close⟩, hc⟩
  -- Keep both lifts but move their coordinate at `e*_a`: being close is an open condition.
  obtain ⟨h_open_pairs, -, -⟩ := F.isOpen_closePairs_and_zero_mem_and_isCompact_closure
  have h_open : IsOpen {r : (T.G × T.G) × A | ((r.1.1⁻¹ : T.G) *ᵥ update w (eStar a) r.2,
      ((r.1.1 * r.1.2)⁻¹ : T.G) *ᵥ update w' (eStar a) r.2) ∈ F.closePairs} :=
    h_open_pairs.preimage (by fun_prop)
  have hc' : w' (eStar a) = c := (h_congr.apply_eStar a.is_lt.le a).trans hc
  have h_mem : ((x⁻¹ : T.G) *ᵥ update w (eStar a) c,
      ((x * y)⁻¹ : T.G) *ᵥ update w' (eStar a) c) ∈ F.closePairs := by
    rwa [update_eq_self_iff.2 hc.symm, update_eq_self_iff.2 hc'.symm]
  filter_upwards [h_open.mem_nhds h_mem] with r hr
  have h_orth_update : IsOrthogonalBelow a (update w (eStar a) r.2) := by
    intro b hb
    have h_ne : (eStar b : 𝔰.BesselIndex) ≠ eStar a := by grind
    rw [update_of_ne h_ne, h_orth b hb]
  have h_congr_update : CongrBelow a (update w (eStar a) r.2) (update w' (eStar a) r.2) := by
    intro k hk
    by_cases h_eq : k = eStar a
    · simp [h_eq]
    · simp [h_eq, h_congr k hk]
  exact ⟨update w (eStar a) r.2, ⟨h_orth_update, _, h_congr_update, hr⟩, by simp⟩

/-- The set 𝔡_a = `F.stableProducts a x y` of the points x and x y does not change when both points
are moved by an element ξ of R^(a+1) = `partialUnitriangularGroup (a + 1)`. -/
lemma stableProducts_mul_left (hξ : ξ ∈ partialUnitriangularGroup (a + 1)) :
    F.stableProducts a (ξ * x) y = F.stableProducts a x y := by
  -- Move both lifts of a stable vector by `ξ`.
  have h_subset {ξ x : T.G} (hξ : ξ ∈ partialUnitriangularGroup (a + 1)) :
      F.stableProducts a x y ⊆ F.stableProducts a (ξ * x) y := by
    rintro _ ⟨w, ⟨h_orth, w', h_congr, h_close⟩, rfl⟩
    have h_close_mul : ((ξ * x)⁻¹.val.val *ᵥ ξ.val.val *ᵥ w,
        (ξ * x * y)⁻¹.val.val *ᵥ ξ.val.val *ᵥ w') ∈ F.closePairs := by
      simpa [mul_assoc] using h_close
    have h_stable : F.IsStable a (ξ * x) (ξ * x * y) (ξ.val.val *ᵥ w) :=
      ⟨h_orth.mulVec hξ a.val.le_succ, ξ.val.val *ᵥ w',
        h_congr.mulVec hξ a.val.le_succ a.is_lt.le, h_close_mul⟩
    exact ⟨_, h_stable, partialUnitriangularGroup_mulVec_eStar hξ a.val.lt_succ_self h_orth⟩
  refine Subset.antisymm ?_ (h_subset hξ)
  simpa using h_subset (x := ξ * x) (inv_mem hξ)

/-- The set 𝔡_a of the points x and y, which is `F.stableProducts a x (x⁻¹ * y)`, does not change
when y alone is moved by an element ν of U_(<a) = `unipotentBelow a`. -/
lemma stableProducts_unipotentBelow_mul {ν : T.G} (hν : ν ∈ unipotentBelow a) :
    F.stableProducts a x (x⁻¹ * (ν * y)) = F.stableProducts a x (x⁻¹ * y) := by
  -- Replace the lift `w'` at the second point by `ν w'`.
  have h_subset {ν y : T.G} (hν : ν ∈ unipotentBelow a) :
      F.stableProducts a x (x⁻¹ * y) ⊆ F.stableProducts a x (x⁻¹ * (ν * y)) := by
    rintro _ ⟨w, ⟨h_orth, w', h_congr, h_close⟩, rfl⟩
    have h_orth' : IsOrthogonalBelow a w' := h_orth.of_congrBelow h_congr a.is_lt.le
    have h_congr_mul : CongrBelow a w (ν *ᵥ w') := h_congr.trans (h_orth'.congrBelow_mulVec hν)
    exact ⟨w, ⟨h_orth, ν *ᵥ w', h_congr_mul, by simpa using h_close⟩, rfl⟩
  refine Subset.antisymm ?_ (h_subset hν)
  simpa using h_subset (y := ν * y) (inv_mem hν)

/-- For all x, y in the unitary group `T.G`, the subset 𝔡_a = `F.stableProducts a x y` of A has
nonzero finite volume. -/
@[simp]
lemma volume_stableProducts_ne_zero_ne_top :
    volume (F.stableProducts a x y) ≠ 0 ∧ volume (F.stableProducts a x y) ≠ ∞ := by
  -- The set is open, contains `0`, and lies in a continuous image of the compact closure of the set
  -- of close pairs.
  obtain ⟨-, h_zero_mem, h_compact_pairs⟩ := F.isOpen_closePairs_and_zero_mem_and_isCompact_closure
  have h_open : IsOpen (F.stableProducts a x y) :=
    isOpen_setOf_mem_stableProducts.preimage (.prodMk_right (x, y))
  have h_zero : F.IsShortFrom x (x * y) 0 := by
    simpa [IsShortFrom, Prod.mk_zero_zero] using h_zero_mem
  have h_nonempty : (F.stableProducts a x y).Nonempty :=
    ⟨0, 0, h_zero.isStable fun _ _ ↦ rfl, rfl⟩
  let f : (𝔰.BesselIndex → A) × (𝔰.BesselIndex → A) → A :=
    fun w ↦ (x *ᵥ w.1 : 𝔰.BesselIndex → A) (eStar a)
  have h_compact : IsCompact (f '' closure F.closePairs) := h_compact_pairs.image (by fun_prop)
  have h_subset : F.stableProducts a x y ⊆ f '' closure F.closePairs := by
    rintro _ ⟨w, ⟨-, w', -, h_close⟩, rfl⟩
    exact ⟨_, subset_closure h_close, by simp [f]⟩
  exact ⟨h_open.measure_ne_zero _ h_nonempty,
    measure_ne_top_of_subset h_subset h_compact.measure_ne_top⟩

/-- The depth, the inverse of the volume of 𝔡_a, is nonzero. -/
lemma depth_ne_zero : F.depth a x y ≠ 0 :=
  ENNReal.inv_ne_zero.2 volume_stableProducts_ne_zero_ne_top.right

/-- The depth, the inverse of the volume of 𝔡_a, is finite. -/
lemma depth_ne_top : F.depth a x y ≠ ∞ :=
  ENNReal.inv_ne_top.2 volume_stableProducts_ne_zero_ne_top.left

/-- The depth of e_a at the points x and x y does not change when both points are moved by an
element ξ of `partialUnitriangularGroup (a + 1)`. -/
lemma depth_mul_left (hξ : ξ ∈ partialUnitriangularGroup (a + 1)) :
    F.depth a (ξ * x) y = F.depth a x y := by
  rw [depth, depth, stableProducts_mul_left hξ]

/-- The depth of e_a at the points x and y does not change when y alone is moved by an element ν
of `unipotentBelow a`. -/
lemma depth_unipotentBelow_mul {ν : T.G} (hν : ν ∈ unipotentBelow a) :
    F.depth a x (x⁻¹ * (ν * y)) = F.depth a x (x⁻¹ * y) := by
  rw [depth, depth, stableProducts_unipotentBelow_mul hν]

lemma le_depth_iff {D : ℝ≥0∞} : D ≤ F.depth a x y ↔ volume (F.stableProducts a x y) ≤ D⁻¹ :=
  ENNReal.le_inv_iff_le_inv

/-- The depth of e_a is a measurable function of the pair (x, y). -/
@[fun_prop] lemma measurable_depth : Measurable ↿(F.depth a) :=
  (measurable_measure_prodMk_left isOpen_setOf_mem_stableProducts.measurableSet).inv

open U in
/-- Let X' be the span of the columns of `F.orthonormalPart`, and let W be the set of common vectors
for g, x and v: the w in X' killed by the rows of v and short from g and g x. Let φ(u) bound the
inverse volume of ⟨u, W⟩, and let σ move W to vectors orthogonal to the e_b, b < a. Then the depth
of e_a at σ g and σ g x, the inverse volume of `F.stableProducts a (σ * g) x`, is at most φ(y_X),
where y = σ⁻¹ e_a = `orbitPoint a.castSucc σ` and y_X is the vector of the products of the basis
vectors of X' with y. -/
lemma IsCommonBound.depth_le {v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A}
    {φ : (F.FreeIndex → A) → ℝ≥0∞} {Λ : ℝ≥0∞} {S : Size T}
    (hφ : F.IsCommonBound S Λ (F.commonVectors g x v) φ)
    (h_orth : ∀ w ∈ F.commonVectors g x v,
      IsOrthogonalBelow a (σ *ᵥ F.orthonormalPart *ᵥ w : 𝔰.BesselIndex → A)) :
    F.depth a (σ * g) x ≤ φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ orbitPoint a.castSucc σ) := by
  -- For a common vector `w`, the vector `σ w` is stable, and `⟨e_a, σ w⟩ = ⟨y, w⟩`.
  have h_mem (w : F.FreeIndex → A) (hw : w ∈ F.commonVectors g x v) :
      star (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ orbitPoint a.castSucc σ) ⬝ᵥ w ∈
        F.stableProducts a (σ * g) x := by
    have h_short : F.IsShortFrom (σ * g) (σ * g * x) (σ *ᵥ F.orthonormalPart *ᵥ w) := by
      obtain ⟨-, hw_short⟩ := hw
      simpa [IsShortFrom, mul_assoc] using hw_short
    have h_frame : σ *ᵥ orbitPoint a.castSucc σ = Pi.single (𝔰.besselFrame a.castSucc) 1 :=
      orbitPoint_eq_iff.1 rfl
    have h_form : (σ *ᵥ F.orthonormalPart *ᵥ w : 𝔰.BesselIndex → A) (eStar a) =
        star (orbitPoint a.castSucc σ) ⬝ᵥ T.splitGram *ᵥ F.orthonormalPart *ᵥ w := by
      rw [← form_mulVec_mulVec σ, h_frame]
      simp [-mulVec_mulVec]
    refine ⟨_, h_short.isStable (h_orth w hw), h_form.trans ?_⟩
    simp only [star_mulVec_dotProduct, conjTranspose_conjTranspose,
      IsHermitianUnit.conjTranspose_eq]
  refine le_trans ?_ (hφ.inv_volume_le _)
  rw [depth]
  gcongr
  rintro _ ⟨w, hw, rfl⟩
  exact h_mem w hw

/-- The weight of length a + 1 is the weight of length a times depth^(-s) of e_a, where
s = `F.volumeExponent`. -/
lemma depthWeight_succ :
    F.depthWeight (a + 1) x y = F.depthWeight a x y * (F.depth a x y)⁻¹ ^ F.volumeExponent := by
  simp [depthWeight, filter_gt_eq_Iio, prod_Iio_mul_eq_prod_Iic, filter_ge_eq_Iic]

/-- The weight of length j, the product of the powers depth^(-s), is nonzero and finite. -/
@[simp] lemma depthWeight_ne_zero_and_ne_top :
    F.depthWeight j x y ≠ 0 ∧ F.depthWeight j x y ≠ ∞ := by
  simp [depthWeight, depth_ne_zero, depth_ne_top, prod_ne_top, prod_eq_zero_iff]

/-- The quotient of the weights of lengths a and a + 1 is the s-th power of the depth of e_a, where
s = `F.volumeExponent`. -/
lemma depthWeight_div_succ :
    F.depthWeight a x y / F.depthWeight (a + 1) x y = F.depth a x y ^ F.volumeExponent := by
  simp [depthWeight_succ, division_def, ENNReal.mul_inv, ENNReal.mul_inv_cancel_left,
    ENNReal.inv_pow]

/-- The weight of length j at the points x and x y does not change when both points are moved by an
element ξ of `partialUnitriangularGroup j`. -/
@[simp] lemma depthWeight_mul_left (h : ξ ∈ partialUnitriangularGroup j) :
    F.depthWeight j (ξ * x) y = F.depthWeight j x y := by
  refine prod_congr rfl fun a ha ↦ ?_
  have h_succ : ξ ∈ partialUnitriangularGroup (a + 1) := by grind
  rw [depth_mul_left h_succ]

/-- The function `F.invDepthWeight j x`, the inverse of the weight of length j on the points near at
j and zero elsewhere, is left invariant under `partialUnitriangularGroup j`. -/
@[simp]
lemma invDepthWeight_mul_left (h : ξ ∈ partialUnitriangularGroup j) :
    F.invDepthWeight j x (ξ * g) = F.invDepthWeight j x g := by
  classical
  simp [invDepthWeight, indicator, h]

end PlaceData

/-- The weight of length j is a measurable function of the pair (x, y). -/
@[fun_prop] lemma measurable_depthWeight : Measurable ↿(F.depthWeight j) := by
  change Measurable fun r : T.G × T.G ↦
    ∏ a : Fin 𝔰.ϱ with a.val < j, (F.depth a r.1 r.2)⁻¹ ^ F.volumeExponent
  exact measurable_prod _ fun a _ ↦ (F.measurable_depth (a := a)).inv.pow_const _

/-- The function `F.invDepthWeight j x`, the inverse of the weight of length j on the points near at
j and zero elsewhere, is measurable. -/
@[fun_prop]
lemma PlaceData.measurable_invDepthWeight : Measurable (F.invDepthWeight j x) :=
  .indicator (by fun_prop) measurableSet_isNear

end New.Floors

namespace New.Floors.Gauge

open Matrix MeasureTheory BesselIndex ENNReal Fintype FloorGroups ProbabilityTheory Size Set
  PlaceData U
  Place Finset

variable {A ι : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {𝔰 : Shape} [Fintype ι] [DecidableEq ι] {m j : ℕ} {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} (Γ : Gauge F) {x : T.G} (a : Fin 𝔰.ϱ) {p : ℕ → Aˣ}

/-- A combination of the orthonormal vectors, the columns of `F.orthonormalPart`, is orthogonal to
the frame vectors e_b with b < l and b < ϱ. -/
lemma isOrthogonalBelow_orthonormalPart_mulVec {l : ℕ} (w : F.FreeIndex → A) :
    IsOrthogonalBelow l (F.orthonormalPart *ᵥ w) :=
  fun b _ ↦ by simp

/-- Deep vectors are rare. For x in the set `F.positions` and every g, take the s-th power of the
depth of e_a at σ g and σ g x. Integrate it for the measure `F.floorMeasure a` in σ, over the σ with
σ g near at a + 1. The integral is at most Λ^(10⁴ n) (`F.FloorMassLe`), where Λ = `Γ.loss` is the
constant of the gauge and n = `𝔰.n`. -/
lemma floorMassLe_depth_pow (hx : x ∈ F.positions) :
    F.FloorMassLe a (Γ.loss ^ (10 ^ 4 * 𝔰.n)) fun g : T.G ↦ F.depth a g x ^ F.volumeExponent := by
  -- For `g` in the box `F.boxSet` the depth at `σ * g` is at most `φ(y_X)`, where `y = σ⁻¹ e_a`.
  refine Γ.floorMassLe_of_chart (b := a.castSucc) (fun ξ hξ g ↦ ?_) fun g hg ↦ ?_
  · simp only [depth_mul_left hξ]
  obtain ⟨φ, hφ⟩ : ∃ φ : (F.FreeIndex → A) → ℝ≥0∞,
      F.IsCommonBound Γ.toSize Γ.loss (F.commonVectors g x 0) φ := Γ.exists_commonBound g hg x hx 0
  have hφ_meas : Measurable φ := hφ.measurable
  have h_depth (σ : T.G) (hσ : σ ∈ floorGroup a) :
      F.depth a (σ * g) x ≤ φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ orbitPoint a.castSucc σ) :=
    hφ.depth_le fun w _ ↦ (isOrthogonalBelow_orthonormalPart_mulVec w).mulVec
      (mem_partialUnitriangularGroup_of_mem_floorGroup hσ) le_rfl
  let Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞ :=
    fun v ↦ φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ v) ^ F.volumeExponent
  -- The bound over size `7` on the quadric comes from the bound over size `7 + 4` on X', at the
  -- cost of a factor `Λ ^ (99 n (7 + 6))`.
  have h_free : ∫⁻ u in Γ.vecsOfSize 11, φ u ^ F.volumeExponent ≤ Γ.loss ^ (99 * 𝔰.n * 12) :=
    hφ.lintegral_le 11
  have h_quadric : ∫⁻ v in Γ.vecsOfSize 7, Ψ v ∂F.floorQuadricMeasure a.castSucc ≤
      Γ.loss ^ (10 ^ 4 * 𝔰.n) :=
    calc
      _ ≤ Γ.loss ^ (99 * 𝔰.n * 13) * Γ.loss ^ (99 * 𝔰.n * 12) :=
        setLIntegral_orthonormalPart_le (j := 7) (hρ := .inr rfl) h_free
      _ = Γ.loss ^ (99 * 𝔰.n * 13 + 99 * 𝔰.n * 12) := by rw [pow_add]
      _ ≤ Γ.loss ^ (10 ^ 4 * 𝔰.n) := pow_le_pow_right₀ Γ.one_le_loss (by lia)
  exact ⟨Ψ, h_quadric, by fun_prop, fun σ hσ ↦ pow_le_pow_left' (h_depth σ hσ) _⟩

/-- The bound Λ^(10⁶ n³) for all floors of a head together: at most n floors at Λ^(10⁶ n²) each,
with n = `𝔰.n` and Λ = `Γ.loss`, the constant of the gauge. -/
noncomputable abbrev floorsConst : ℝ≥0∞ := Γ.loss ^ (10 ^ 6 * 𝔰.n ^ 3)

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- An element g of `floorGroup l` does not change the coordinate of a vector at e_c for c < l. -/
lemma mulVec_apply_inl_of_mem_floorGroup {l : ℕ} {g : T.G} {c : Fin 𝔰.ϱ} (hg : g ∈ floorGroup l)
    (hc : c < l) (v : 𝔰.BesselIndex → A) :
    (g *ᵥ v : 𝔰.BesselIndex → A) (Sum.inl c) = v (Sum.inl c) := by
  have h_row (i : 𝔰.BesselIndex) :
      g.val (Sum.inl c) i = (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) (Sum.inl c) i :=
    apply_eq_one_apply_of_mem_floorGroup hg (Sum.inl c) i (.inl ⟨hc, c.is_lt⟩)
  conv_rhs => rw [← one_mulVec v]
  exact sum_congr rfl fun i _ ↦ congrArg (· * v i) (h_row i)

/-- Let the head p of length a + 1 be adapted (`Γ.IsHead`), x in `F.positions`, y in the box
`F.boxSet` and ν in `unipotentBelow a`, and write w_p for the Weyl element `weylElem (a + 1) p`. The
integral of the s-th power of the depth `F.depth a z x`, the inverse volume of
`F.stableProducts a z x`, at z = w_p n ν y, over the n in the Heisenberg group of floor a with z
near at a + 1, is at most |p_a|^(-r-1/2) Λ^(10⁶ n²). Here Λ = `Γ.loss`, the first factor is
`F.floorModulus a (p a)⁻¹`, and r = k + 1 + 2 (ϱ - a - 1). -/
lemma lintegral_depth_pow_section_le {y ν : T.G} (hp : Γ.IsHead (a + 1) p) (hx : x ∈ F.positions)
    (hy : y ∈ F.boxSet) (hν : ν ∈ unipotentBelow a) :
    ∫⁻ n : T.G, {z : T.G | F.IsNear (a + 1) z}.indicator
        (fun z : T.G ↦ F.depth a z x ^ F.volumeExponent) (weylElem (a + 1) p * (n * ν) * y)
      ∂heisenbergMeasure a ≤ F.floorModulus a (p a)⁻¹ * Γ.loss ^ (10 ^ 6 * (𝔰.n * 𝔰.n)) := by
  -- The vector `(w_p n ν)⁻¹ e_a` is a lift of a point `z` of the section `⟨e_a, z⟩ = star (p a)`.
  -- Its depth is at most `φ(z_X)`, for the common vectors orthogonal to the earlier vectors
  -- `(w_p n ν)⁻¹ e_b`, which are multiples of the `ν⁻¹ e*_b`.
  let forms : Matrix (Fin 𝔰.ϱ) F.FreeIndex A := (ν.val.val * F.orthonormalPart).toRows₁
  obtain ⟨φ, hφ⟩ : ∃ φ : (F.FreeIndex → A) → ℝ≥0∞,
      F.IsCommonBound Γ.toSize Γ.loss (F.commonVectors y x forms) φ :=
        Γ.exists_commonBound y hy x hx forms
  have hφ_meas : Measurable φ := hφ.measurable
  let c : Aˣ := star (p a)
  have h_depth (n : T.G) (hn : n ∈ floorUnipotent a) :
      F.depth a (weylElem (a + 1) p * (n * ν) * y) x ≤
        φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ sectionPoint a c.val n) := by
    have hn_floor : n ∈ floorGroup a := (Subgroup.mem_inf.1 hn).left
    have h_orth (w : F.FreeIndex → A) (hw : w ∈ F.commonVectors y x forms) :
        IsOrthogonalBelow a ((weylElem (a + 1) p * (n * ν) : T.G) *ᵥ F.orthonormalPart *ᵥ w :
          𝔰.BesselIndex → A) := by
      intro b hb
      have hw_ker : forms *ᵥ w = 0 := hw.left
      have h_zero : (ν *ᵥ F.orthonormalPart *ᵥ w : 𝔰.BesselIndex → A) (Sum.inl b) = 0 := by
        rw [mulVec_mulVec]
        exact congrFun hw_ker b
      have h_assoc : (weylElem (a + 1) p * (n * ν)).val.val *ᵥ F.orthonormalPart *ᵥ w =
          (weylElem (a + 1) p : T.G).val.val *ᵥ n.val.val *ᵥ ν.val.val *ᵥ
            F.orthonormalPart *ᵥ w := by
        simp only [mulVec_mulVec, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
      rw [h_assoc, weylElem_mulVec_eStar (hb.trans a.val.lt_succ_self),
        mulVec_apply_inl_of_mem_floorGroup hn_floor hb, h_zero, mul_zero]
    exact (hφ.depth_le h_orth).trans_eq (congrArg φ
      ((congrBelow_sectionPoint_orbitPoint hn_floor hν).orthonormalPart_conjTranspose_mulVec_eq
        a.is_lt.le))
  let Ψ : (𝔰.BesselIndex → A) → ℝ≥0∞ := (Γ.vecsOfSize (20 * 𝔰.n)).indicator fun z ↦
    φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ z) ^ F.volumeExponent
  have hΨ : Measurable Ψ := .indicator (by fun_prop) measurableSet_vecsOfSize
  have h_point (n : T.G) (hn : n ∈ floorUnipotent a) :
      {z : T.G | F.IsNear (a + 1) z}.indicator (fun z : T.G ↦ F.depth a z x ^ F.volumeExponent)
        (weylElem (a + 1) p * (n * ν) * y) ≤ Ψ (sectionPoint a c.val n) := by
    refine indicator_apply_le' (fun h_near ↦ ?_) fun _ ↦ zero_le
    have h_size : sectionPoint a c.val n ∈ Γ.vecsOfSize (20 * 𝔰.n) :=
      sectionPoint_mem_vecsOfSize_of_isNear hp hy hn hν h_near
    simp only [Ψ, indicator_of_mem h_size]
    exact pow_le_pow_left' (h_depth n hn) _
  have h_section : ∫⁻ z, Ψ z ∂sectionMeasure T a c ≤
      modulus (p a)⁻¹.val ^ (2⁻¹ : ℝ) * Γ.loss ^ (10 ^ 6 * (𝔰.n * 𝔰.n)) := by
    have h_modulus : modulus c⁻¹.val = modulus (p a)⁻¹.val := by simp [c]
    have h_exp : 20 * 𝔰.n + 3 + (99 * 𝔰.n * (20 * 𝔰.n + 7) + 99 * 𝔰.n * (20 * 𝔰.n + 5 + 1)) ≤
        10 ^ 6 * (𝔰.n * 𝔰.n) := by
      nlinarith
    grw [lintegral_indicator measurableSet_vecsOfSize,
      setLIntegral_sectionMeasure_le c (hφ.lintegral_le (20 * 𝔰.n + 5)), ← pow_add, ← pow_add,
      h_modulus, pow_le_pow_right₀ Γ.one_le_loss h_exp]
  have h_heisenberg : ∫⁻ n, Ψ (sectionPoint a c.val n) ∂heisenbergMeasure (T := T) a =
      modulus (p a)⁻¹.val ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))) * ∫⁻ z, Ψ z ∂sectionMeasure T a c := by
    simp [sectionMeasure, lintegral_map hΨ (measurable_sectionPoint _), c, ← mul_assoc, ← mul_pow,
      ENNReal.inv_mul_cancel]
  grw [lintegral_le_of_ae_imp ae_mem_floorUnipotent h_point, h_heisenberg, h_section, floorModulus,
    mul_assoc]

/-- For z near at j, `F.invDepthWeight j x z` is the product over the floors l < j of the s-th
powers, s = `F.volumeExponent`, of the depths of e_l at z and z x. Let the head p of length a + 1 be
adapted (`Γ.IsHead`), x in `F.positions`, y in the box `F.boxSet` and ν in `unipotentBelow a`. The
integral over the n in the Heisenberg group of floor a of the inverse weight of length a + 1 at
`weylElem (a + 1) p` n ν y is at most the inverse weight of length a at `weylElem a p` ν y, times
`F.floorModulus a (p a)⁻¹` and the power 10⁶ `𝔰.n`² of the constant `Γ.loss` of the gauge. -/
lemma lintegral_invDepthWeight_succ_le {y ν : T.G} (hp : Γ.IsHead (a + 1) p) (hx : x ∈ F.positions)
    (hy : y ∈ F.boxSet) (hν : ν ∈ unipotentBelow a) :
    ∫⁻ n : T.G, F.invDepthWeight (a + 1) x (weylElem (a + 1) p * (n * ν * y)) ∂heisenbergMeasure a ≤
      F.invDepthWeight a x (weylElem a p * (ν * y)) *
        (F.floorModulus a (p a)⁻¹ * Γ.loss ^ (10 ^ 6 * (𝔰.n * 𝔰.n))) := by
  have h_near_meas : MeasurableSet {z : T.G | F.IsNear (a + 1) z} := measurableSet_isNear
  have h_split (n : T.G) (hn : n ∈ floorUnipotent a) :
      F.invDepthWeight (a + 1) x (weylElem (a + 1) p * (n * ν * y)) ≤
        F.invDepthWeight a x (weylElem a p * (ν * y)) * {z : T.G | F.IsNear (a + 1) z}.indicator
          (fun z : T.G ↦ F.depth a z x ^ F.volumeExponent) (weylElem (a + 1) p * (n * ν) * y) := by
    rw [← mul_assoc]
    set z : T.G := weylElem (a + 1) p * (n * ν) * y with hz
    -- the weight of length `a` does not see the new Weyl and Heisenberg factors
    have h_lower : F.invDepthWeight a x z = F.invDepthWeight a x (weylElem a p * (ν * y)) := by
      simp [hz, weylElem_succ, weylElem_mul_left_comm, Subgroup.mem_inf.mp hn, mul_assoc]
    rw [← h_lower]
    obtain h_far | h_near := em' (F.IsNear (a + 1) z)
    · simp [invDepthWeight, h_far]
    · simp [invDepthWeight, h_near, h_near.anti a.val.le_succ, depthWeight_succ, ENNReal.mul_inv,
        ENNReal.inv_pow]
  grw [lintegral_le_of_ae_imp ae_mem_floorUnipotent h_split, lintegral_const_mul _ (by fun_prop),
    Γ.lintegral_depth_pow_section_le a hp hx hy hν]

/-- The integral of the inverse weight. Let the head p of length j ≤ ϱ be adapted (`Γ.IsHead`), x a
position and g near at j (ξ g lies in the box for some ξ in `partialUnitriangularGroup j`). Let
w_p = `weylElem j p`. The integral of the inverse weight `F.invDepthWeight j x` at w_p ν g, for the
convolution of the Heisenberg measures of the floors below j in the variable ν, is at most
`Γ.floorsConst` = Λ^(10⁶ n³) times the product over a < j of the
|p_a|^(-r_a-1/2) = `F.floorModulus a (p a)⁻¹`. -/
lemma lintegral_invDepthWeight_le {g : T.G} (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hx : x ∈ F.positions) (h_near : F.IsNear j g) :
    ∫⁻ ν : T.G, F.invDepthWeight j x (weylElem j p * (ν * g)) ∂ascConv heisenbergMeasure j ≤
      (∏ a ∈ Finset.range j, F.floorModulus a (p a)⁻¹) * Γ.floorsConst := by
  -- Move `g` into the box `F.boxSet`, then use induction on the length of the head.
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup j, ξ * g ∈ F.boxSet := h_near
  obtain ⟨γ, hγ, n, hn, rfl⟩ : ∃ γ ∈ floorGroup j, ∃ n ∈ unipotentBelow j, ξ = γ * n :=
    exists_floorGroup_mul_unipotentBelow hξ
  have h_floors (a : ℕ) (ha : a ≤ j) :
      ∫⁻ ν, F.invDepthWeight a x (weylElem a p * (ν * (γ * n * g))) ∂ascConv heisenbergMeasure a ≤
        (∏ l ∈ .range a, F.floorModulus l (p l)⁻¹) * Γ.loss ^ (10 ^ 6 * (𝔰.n * (𝔰.n * a))) := by
    induction a with
    | zero => simp [invDepthWeight, depthWeight, ascConv, indicator_apply_le']
    | succ a ih =>
      lift a to Fin 𝔰.ϱ using ha.trans hj
      have hp_succ : Γ.IsHead (a + 1) p := fun l hl ↦ hp l (hl.trans ha)
      calc
        _ = ∫⁻ ν, ∫⁻ u, F.invDepthWeight (a + 1) x (weylElem (a + 1) p * (u * ν * (γ * n * g)))
              ∂heisenbergMeasure a ∂ascConv heisenbergMeasure a := by
          rw [ascConv_heisenbergMeasure_succ, lintegral_mconv_symm (by fun_prop)]
        _ ≤ ∫⁻ ν, F.invDepthWeight a x (weylElem a p * (ν * (γ * n * g))) *
              (F.floorModulus a (p a)⁻¹ * Γ.loss ^ (10 ^ 6 * (𝔰.n * 𝔰.n)))
              ∂ascConv heisenbergMeasure a :=
          lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν hν ↦
            Γ.lintegral_invDepthWeight_succ_le a hp_succ hx h_box hν
        _ ≤ _ := by
          grw [lintegral_mul_const _ (by fun_prop), ih (by lia), prod_range_succ]
          exact le_of_eq (by ring)
  have h_right_inv : ascConv heisenbergMeasure j ∗ₘ .dirac n = ascConv heisenbergMeasure j :=
    (ascConv_heisenbergMeasure_invariant hn).left
  calc ∫⁻ ν, F.invDepthWeight j x (weylElem j p * (ν * g)) ∂ascConv heisenbergMeasure j
    _ = ∫⁻ ν, F.invDepthWeight j x (weylElem j p * (γ⁻¹ * ν * γ * n * g))
          ∂ascConv heisenbergMeasure j := by
      -- the measure is invariant under `n` and under conjugation by `γ`
      conv_lhs => rw [← h_right_inv, lintegral_mconv_dirac,
        lintegral_eq_of_dirac_mconv_eq (ascConv_heisenbergMeasure_dirac_comm γ hγ)]
    _ = ∫⁻ ν, F.invDepthWeight j x (weylElem j p * (ν * (γ * n * g))) ∂ascConv heisenbergMeasure
      j := by
      -- `γ⁻¹` commutes with `weylElem j p` and does not change the weight
      simp [weylElem_mul_left_comm, hγ, mul_assoc]
    _ ≤ (∏ l ∈ .range j, F.floorModulus l (p l)⁻¹) * Γ.loss ^ (10 ^ 6 * (𝔰.n * (𝔰.n * j))) :=
      h_floors j le_rfl
    _ ≤ _ := by
      have hj_le : j ≤ 𝔰.n := hj.step
      grw [floorsConst, pow_three, ← Nat.mul_le_mul_left _ hj_le]
      exact Γ.one_le_loss

/-- Let the head p of length j ≤ ϱ be adapted, x a position and j ≤ b. Let Φ be measurable, left
invariant under `partialUnitriangularGroup b` and zero off the points near at b. Integrate Φ(g)
times the inverse weight at `weylElem j p * g` against the convolution of the Heisenberg measures of
the floors below j with a measure ρ. The result is at most the product over a < j of the
`F.floorModulus a (p a)⁻¹`, times `Γ.floorsConst`, times the integral of Φ against ρ. -/
lemma lintegral_mul_invDepthWeight_le {b : ℕ} {Φ : T.G → ℝ≥0∞} {ρ : Measure T.G} [SFinite ρ]
    (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p) (hx : x ∈ F.positions) (hjb : j ≤ b)
    (hΦ : (partialUnitriangularGroup b).FixesLeft Φ ∧ ∀ g : T.G, ¬F.IsNear b g → Φ g = 0)
    (hΦ_meas : Measurable Φ) :
    ∫⁻ g : T.G, Φ g * F.invDepthWeight j x (weylElem j p * g) ∂ascConv heisenbergMeasure j ∗ₘ ρ ≤
      (∏ a ∈ Finset.range j, F.floorModulus a (p a)⁻¹) * Γ.floorsConst * ∫⁻ g : T.G, Φ g ∂ρ := by
  obtain ⟨hΦ_inv, hΦ_zero⟩ := hΦ
  rw [lintegral_mconv_symm (by fun_prop), mul_comm, ← lintegral_mul_const _ hΦ_meas]
  gcongr with y
  have h_pull (ν : T.G) (hν : ν ∈ unipotentBelow j) :
      Φ (ν * y) * F.invDepthWeight j x (weylElem j p * (ν * y)) =
        Φ y * F.invDepthWeight j x (weylElem j p * (ν * y)) := by
    rw [hΦ_inv ν (unipotentBelow_le_partialUnitriangularGroup hν)]
  rw [lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow h_pull,
    lintegral_const_mul _ (by fun_prop)]
  by_cases h_near : F.IsNear b y
  · grw [Γ.lintegral_invDepthWeight_le hj hp hx (h_near.anti hjb)]
  · simp [hΦ_zero y h_near]

/-- The cost of floor l on the position ball: |M|^(r_l+1/2) c^(rank X') Λ^(4900 n), where
|M|^(r_l+1/2) = `F.floorModulus l`, c = `P.kernelBound` and X' has the basis `F.FreeIndex`. -/
noncomputable abbrev floorConst (l : ℕ) : ℝ≥0∞ :=
  F.floorModulus l * P.kernelBound ^ Fintype.card F.FreeIndex * Γ.loss ^ (4900 * 𝔰.n)

/-- An identity for the Heisenberg group of floor a. Let ⟨·, ·⟩ be the form of `T.splitGram`. For
t = (ω, β) let n = `P.heisenbergElem a t`, with ω extended by zero. Let ζ, ζ' be congruent modulo
the e_b, b < a, and let o be orthogonal to the e_b, b ≤ a. Then ⟨ζ, o⟩ - ⟨n⁻¹ ζ', o⟩ is the
conjugate of ⟨e_a, ζ⟩ = `ζ (eStar a)` times ⟨ω, o⟩. -/
lemma form_sub_form_heisenbergElem_inv_mulVec {ζ ζ' o : 𝔰.BesselIndex → A}
    (h_congr : CongrBelow a ζ ζ') (ho : IsOrthogonalBelow (a + 1) o)
    (t : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) :
    star ζ ⬝ᵥ T.splitGram *ᵥ o -
        star ((P.heisenbergElem (T := T) a t)⁻¹.val.val *ᵥ ζ') ⬝ᵥ T.splitGram *ᵥ o =
      star (ζ (eStar a)) * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ T.splitGram *ᵥ o := by
  set n : T.G := P.heisenbergElem a t with hn
  set ω : 𝔰.BesselIndex → A := inclMatrix A Subtype.val *ᵥ t.1 with hω
  have h_move : n *ᵥ o = o - (star ω ⬝ᵥ T.splitGram *ᵥ o) • Pi.single (Sum.inl a) 1 := by
    simp [hn, hω, heisenbergElem_mulVec, ho a a.val.lt_succ_self, sub_eq_add_neg]
  have h_unitary : star ((n⁻¹ : T.G) *ᵥ ζ') ⬝ᵥ T.splitGram *ᵥ o =
      star ζ' ⬝ᵥ T.splitGram *ᵥ n *ᵥ o := by
    simpa using (form_mulVec_mulVec n ((n⁻¹ : T.G) *ᵥ ζ') o).symm
  have h_lift : star ζ' ⬝ᵥ T.splitGram *ᵥ o = star ζ ⬝ᵥ T.splitGram *ᵥ o :=
    h_congr.form_eq_left (fun b hb ↦ ho b (hb.trans a.val.lt_succ_self)) a.isLt.le
  have h_frame : star ζ' ⬝ᵥ T.splitGram *ᵥ Pi.single (Sum.inl a) 1 = star (ζ (eStar a)) := by
    simp [splitGram_col, h_congr.apply_eStar a.isLt.le]
  rw [h_unitary, h_move, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, h_lift, h_frame]
  simp [mul_comm]

/-- The translates under U_(<l) of the points that are close to g: the z for which g⁻¹ ν z is a
close position for some ν in U_(<l). -/
def closeBelow (l : ℕ) (g : T.G) : Set T.G :=
  {z : T.G | ∃ ν ∈ unipotentBelow l, g⁻¹ * (ν * z) ∈ Γ.positionsOfSize}

/-- Two points of the position ball: if g lies in the box K = `F.boxSet` and x, y lie in the
position ball (`Γ.positionsOfSize`), then all entries of (g x (g y)⁻¹ - 1) / M have size 14, where
M = `F.levelUnit` is the level. -/
lemma hasMatrixSize_mul_inv_sub_one {g x y : T.G} (hg : g ∈ F.boxSet) (hx : x ∈ Γ.positionsOfSize)
    (hy : y ∈ Γ.positionsOfSize) :
    Γ.HasMatrixSize 14 (F.levelUnit⁻¹.val • ((g * x * (g * y)⁻¹).val.val - 1)) := by
  have hx_size : Γ.HasMatrixSize 1 (F.levelUnit⁻¹.val • (x.val.val - 1)) := hx.2
  have hy_size : Γ.HasMatrixSize 1 (F.levelUnit⁻¹.val • (y.val.val - 1)) := hy.2
  -- `y = M ((y - 1) / M) - (-1)` has size `3`, so `g y` has size `5` and its inverse size `9`.
  have hy_entries : Γ.HasMatrixSize 3 y.val.val := by
    intro a b
    have h_sub_one : F.levelUnit.val * (F.levelUnit⁻¹.val • (y.val.val - 1)) a b ∈ Γ.ofSize 2 :=
      Γ.mul_mem_ofSize Γ.levelUnit_mem_ofSize (hy_size a b)
    have h_neg_one : -(1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) a b ∈ Γ.ofSize 2 :=
      Γ.neg_mem_iff_and_star_mem_iff.1.2 (HasMatrixSize.one a b)
    simpa using sub_mem_ofSize h_sub_one h_neg_one
  have h_inv : Γ.HasMatrixSize 9 (g * y)⁻¹.val.val :=
    HasMatrixSize.inv (x := g * y) ((Γ.hasMatrixSize_boxSet hg).mul hy_entries)
  have h_diff : Γ.HasMatrixSize 4
      (g.val.val * (F.levelUnit⁻¹.val • (x.val.val - 1) - F.levelUnit⁻¹.val • (y.val.val - 1))) :=
    (Γ.hasMatrixSize_boxSet hg).mul (hx_size.sub hy_size)
  -- The matrix is `g ((x - 1) / M - (y - 1) / M) (g y)⁻¹`, of size `4 + 9 + 1`.
  simpa [mul_assoc, smul_sub, mul_sub, sub_mul] using h_diff.mul h_inv

/-- The range of the coordinates on a Heisenberg group. Let g lie in the box `F.boxSet` and let g⁻¹
y lie in the position ball (`Γ.positionsOfSize`). Let n lie in the Heisenberg group
`floorUnipotent a` of floor a, with g⁻¹ ν n y in the position ball for some ν in `unipotentBelow a`
(`Γ.closeBelow`). Then some vector v differs from (n⁻¹ - 1) e*_a by a combination of the e_b, b < a
(`CongrBelow`), and all entries of `F.levelUnit⁻¹ • v`, that is v divided by the level
`F.levelUnit`, have size 17 for the gauge Γ (`Γ.vecsOfSize 17`). -/
lemma exists_lift_of_mem_closeBelow {g y n : T.G} (hg : g ∈ F.boxSet)
    (hy : g⁻¹ * y ∈ Γ.positionsOfSize) (hn : n ∈ floorUnipotent a)
    (h_close : n * y ∈ Γ.closeBelow a g) :
    ∃ v : 𝔰.BesselIndex → A, CongrBelow a ((n⁻¹.val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
      F.levelUnit⁻¹.val • v ∈ Γ.vecsOfSize 17 := by
  -- Up to a factor in U_(<a), `n⁻¹` is the quotient `y (ν n y)⁻¹` of two points close to `g`.
  obtain ⟨ν, hν, h_pos⟩ : ∃ ν ∈ unipotentBelow a, g⁻¹ * (ν * (n * y)) ∈ Γ.positionsOfSize :=
    h_close
  obtain ⟨hn_floor, -⟩ := Subgroup.mem_inf.1 hn
  set μ : T.G := n⁻¹ * ν⁻¹ * n⁻¹⁻¹ with hμ
  have h_mem : μ ∈ unipotentBelow a := conj_mem_unipotentBelow (inv_mem hn_floor) (inv_mem hν)
  have h_quotient : g * (g⁻¹ * y) * (g * (g⁻¹ * (ν * (n * y))))⁻¹ = μ * n⁻¹ := by
    rw [hμ]
    group
  have h_size : Γ.HasMatrixSize 14 (F.levelUnit⁻¹.val • ((μ * n⁻¹).val.val - 1)) := by
    rw [← h_quotient]
    exact Γ.hasMatrixSize_mul_inv_sub_one hg hy h_pos
  refine ⟨((μ * n⁻¹).val.val - 1) *ᵥ Pi.single (eStar a) 1,
    congrBelow_sub_one_mulVec (inv_mem hn_floor) h_mem, fun i ↦ ?_⟩
  rw [mulVec_single_one]
  -- this vector is a column of the matrix, and size `14` implies size `17`
  exact mem_ofSize_mono (h_size i (eStar a))

omit [TopologicalSpace A] [MeasureSpace A] [Fintype ι] [DecidableEq ι] P
  [IsHermitianUnit T.splitGram] in
/-- Moving a point and a vector by unitary elements: ⟨(g g⁻¹ n y)⁻¹ ζ, (g g⁻¹ y)⁻¹ o⟩ = ⟨n⁻¹ ζ, o⟩
for the form ⟨·, ·⟩ of `T.splitGram`. -/
lemma form_inv_mulVec_inv_mulVec_cancel (g n y : T.G) (ζ o : 𝔰.BesselIndex → A) :
    star ((g * (g⁻¹ * (n * y)))⁻¹.val.val *ᵥ ζ) ⬝ᵥ T.splitGram *ᵥ (g * (g⁻¹ * y))⁻¹.val.val *ᵥ o =
      star (n⁻¹.val.val *ᵥ ζ) ⬝ᵥ T.splitGram *ᵥ o := by
  rw [mul_inv_cancel_left, mul_inv_cancel_left, ← form_mulVec_mulVec y]
  simp

/-- The product of c (ω / M)_X with a vector u of X' is c̄ ⟨ω, u⟩ / M, where M = `F.levelUnit` is
the level, u is read as the combination `F.orthonormalPart *ᵥ u` of the orthonormal vectors, and
y_X = `F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ y`. -/
lemma star_smul_orthonormalPart_dotProduct (c : A) (ω : 𝔰.BesselIndex → A) (u : F.FreeIndex → A) :
    star (c • F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ F.levelUnit⁻¹.val • ω) ⬝ᵥ u =
      F.levelUnit⁻¹.val * (star c * star ω ⬝ᵥ T.splitGram *ᵥ F.orthonormalPart *ᵥ u) := by
  -- `mulVec_mulVec` and `fromRows_mulVec` would merge or unfold the products on the right.
  simp [star_mulVec_dotProduct, mulVec_smul, ← inverse_star_unit, star_levelUnit,
    IsHermitianUnit.conjTranspose_eq, -mulVec_mulVec, -fromRows_mulVec, mul_left_comm]

/-- Let g lie in the box `F.boxSet` and let g⁻¹ y lie in the position ball (`Γ.positionsOfSize`).
Consider the integral of depth^(-s) of e_a at the points g and n y, over the n in the Heisenberg
group of floor a (measure `heisenbergMeasure a`) with n y in `Γ.closeBelow a g`. It is at most
|M|^(r+1/2) Λ^(4600 n), where the first factor is `F.floorModulus a`, Λ = `Γ.loss`, and the n in the
exponent is `𝔰.n`. Here M = `F.levelUnit` is the level, s = `F.volumeExponent`, and r is the number
of coordinates of the vector part of that group. The inverse depth `(F.depth a z x)⁻¹` is the volume
of the products of e_a with the vectors that are stable at z and z x. -/
lemma lintegral_heisenbergMeasure_inv_depth_le {g y : T.G} (hg : g ∈ F.boxSet)
    (hy : g⁻¹ * y ∈ Γ.positionsOfSize) :
    ∫⁻ n : T.G, (Γ.closeBelow a g).indicator
        (fun z : T.G ↦ (F.depth a g (g⁻¹ * z))⁻¹ ^ F.volumeExponent) (n * y)
      ∂heisenbergMeasure a ≤ F.floorModulus a * Γ.loss ^ (4600 * 𝔰.n) := by
  -- Pair a stable vector with the vectors that are common to `g` and `y`: the inverse depth at `g`
  -- and `n(ω, β) y` is at most `φ(ω_X / M)`.
  obtain ⟨φ, hφ⟩ : ∃ φ : (F.FreeIndex → A) → ℝ≥0∞,
      F.IsCommonBound Γ.toSize Γ.loss (F.commonVectors g (g⁻¹ * y) 0) φ :=
        Γ.exists_commonBound g hg _ hy.left 0
  have hφ_meas : Measurable φ := hφ.measurable
  have h_depth (t : ({i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) × skewAdjoint A) :
      (F.depth a g (g⁻¹ * (P.heisenbergElem a t * y)))⁻¹ ≤
        φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ F.levelUnit⁻¹.val • inclMatrix A Subtype.val *ᵥ
          t.1) := by
    grw [depth, inv_inv, ← hφ.volume_le]
    gcongr
    rintro _ ⟨ζ, ⟨-, ζ', h_congr, h_close⟩, rfl⟩ u ⟨-, h_short⟩
    -- the two close pairs are those of the stable vector `ζ` and of the common vector `u`
    refine ⟨_, h_close, _, h_short, ?_⟩
    -- by unitarity `g` and `y` drop out, and the identity for the Heisenberg group is left
    rw [form_mulVec_mulVec, form_inv_mulVec_inv_mulVec_cancel,
      form_sub_form_heisenbergElem_inv_mulVec a h_congr
        (isOrthogonalBelow_orthonormalPart_mulVec u),
      star_smul_orthonormalPart_dotProduct]
  have h_volume : ∫⁻ ω in Γ.vecsOfSize 17,
      φ (F.orthonormalPartᴴ *ᵥ T.splitGram *ᵥ ω) ^ F.volumeExponent ∂floorVolume a.succ ≤
      Γ.loss ^ (99 * 𝔰.n * (17 + 6)) * Γ.loss ^ (99 * 𝔰.n * (17 + 4 + 1)) :=
    setLIntegral_orthonormalPart_le (.inl rfl) (hφ.lintegral_le (17 + 4))
  -- The skew variable adds `17 + 2` to the exponent, and the sum is at most `4600 n` as `n ≥ 1`.
  rw [← one_mul (F.floorModulus a * _)]
  refine lintegral_heisenbergMeasure_le (j := 17) F.levelUnit h_volume
    fun t h_ne ↦ ?_
  have h_close : P.heisenbergElem a t * y ∈ Γ.closeBelow a g := mem_of_indicator_ne_zero h_ne
  constructor
  · exact Γ.exists_lift_of_mem_closeBelow a hg hy (heisenbergElem_mem_floorUnipotent a t) h_close
  · grw [one_mul, indicator_of_mem h_close, h_depth t]

/-- One floor of the weight `F.depthWeight`. The weight of length j is the product over the first j
vectors e_l of depth^(-s), where s = `F.volumeExponent` and the depth `F.depth` is the inverse
volume of 𝔡_l. Let g lie in the box `F.boxSet`. Suppose that C ≠ ∞ bounds, for all y, the integral
of `Γ.positionsOfSize.indicator (F.depthWeight a g)` at g⁻¹ ν y over ν. The measure in ν is
`ascConv heisenbergMeasure a`, the convolution of the Heisenberg measures of the floors below a.
Then for all y the same integral of length a + 1 is at most C |M|^(r+1/2) Λ^(4600 n). Here
|M|^(r+1/2) = `F.floorModulus a`, M = `F.levelUnit` is the level, r is the rank of the vector part
of the Heisenberg group of floor a, Λ = `Γ.loss` and n = `𝔰.n`. -/
lemma lintegral_depthWeight_succ_le {g : T.G} {C : ℝ≥0∞} (hg : g ∈ F.boxSet) (hC_ne : C ≠ ∞)
    (hC : ∀ y : T.G, ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight a g) (g⁻¹ * (ν * y))
      ∂ascConv heisenbergMeasure a ≤ C) (y : T.G) :
    ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g) (g⁻¹ * (ν * y))
      ∂ascConv heisenbergMeasure (a + 1) ≤ C * (F.floorModulus a * Γ.loss ^ (4600 * 𝔰.n)) := by
  have h_meas : MeasurableSet Γ.positionsOfSize := Γ.measurableSet_positionsOfSize
  -- Unless the integral is zero, some `g⁻¹ * (τ * y)` is a close position. Translate by `τ`.
  by_cases h_zero : ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g)
      (g⁻¹ * (ν * y)) ∂ascConv heisenbergMeasure (a + 1) = 0
  · exact h_zero.trans_le zero_le
  obtain ⟨τ, hτ, h_ne⟩ : ∃ τ ∈ unipotentBelow (a + 1),
      Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g) (g⁻¹ * (τ * y)) ≠ 0 :=
    exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow h_zero
  have hy : g⁻¹ * (τ * y) ∈ Γ.positionsOfSize := mem_of_indicator_ne_zero h_ne
  -- On a coset `U_(<a) z` the depth of `e_a` is constant, so it leaves the integral.
  have h_coset (z : T.G) :
      ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g) (g⁻¹ * (ν * z))
        ∂ascConv heisenbergMeasure a ≤ C * (Γ.closeBelow a g).indicator
          (fun z : T.G ↦ (F.depth a g (g⁻¹ * z))⁻¹ ^ F.volumeExponent) z := by
    by_cases hz_zero : ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g)
        (g⁻¹ * (ν * z)) ∂ascConv heisenbergMeasure a = 0
    · exact hz_zero.trans_le zero_le
    obtain ⟨ν₀, hν₀, h_ne⟩ : ∃ ν₀ ∈ unipotentBelow a,
        Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g) (g⁻¹ * (ν₀ * z)) ≠ 0 :=
      exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow hz_zero
    have hz : z ∈ Γ.closeBelow a g := ⟨ν₀, hν₀, mem_of_indicator_ne_zero h_ne⟩
    grw [indicator_of_mem hz, ← hC z, ← lintegral_mul_const _ (by fun_prop)]
    refine lintegral_le_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν hν ↦ ?_
    rw [← indicator_mul_const, ← depth_unipotentBelow_mul hν]
    exact indicator_le_indicator depthWeight_succ.le
  have h_right_inv : ascConv heisenbergMeasure (a + 1) ∗ₘ .dirac τ =
      ascConv heisenbergMeasure (a + 1) :=
    (ascConv_heisenbergMeasure_invariant hτ).left
  calc
    _ = ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g) (g⁻¹ * (ν * τ * y))
          ∂ascConv heisenbergMeasure (a + 1) := by
      conv_lhs => rw [← h_right_inv, lintegral_mconv_dirac]
    _ = ∫⁻ n : T.G, ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight (a + 1) g)
          (g⁻¹ * (ν * (n * (τ * y)))) ∂ascConv heisenbergMeasure a ∂heisenbergMeasure a := by
      -- Fubini: the measure of length `a + 1` is that of length `a` convolved with floor `a`
      rw [ascConv, lintegral_mconv_symm (by fun_prop)]
      simp only [mul_assoc]
    _ ≤ ∫⁻ n : T.G, C * (Γ.closeBelow a g).indicator
          (fun z : T.G ↦ (F.depth a g (g⁻¹ * z))⁻¹ ^ F.volumeExponent) (n * (τ * y))
          ∂heisenbergMeasure a :=
      lintegral_mono fun n ↦ h_coset (n * (τ * y))
    _ ≤ C * (F.floorModulus a * Γ.loss ^ (4600 * 𝔰.n)) := by
      grw [lintegral_const_mul' _ _ hC_ne, Γ.lintegral_heisenbergMeasure_inv_depth_le a hg hy]

/-- The integral of the weight over the position ball. Let j ≤ ϱ and let g be near at j (ξ g lies in
the box for some ξ in `partialUnitriangularGroup j`). The weight `F.depthWeight j` is the product of
the powers depth^(-s), s = `F.volumeExponent`, over the first j frame vectors. Integrate it at the
points g and ν y, over the ν for which g⁻¹ ν y lies in the position ball (`Γ.positionsOfSize`),
against the convolution of the Heisenberg measures of the floors below j. The result is at most the
product of the constants `Γ.floorConst l`, l < j. -/
lemma lintegral_depthWeight_le (hj : j ≤ 𝔰.ϱ) (g y : T.G) (h_near : F.IsNear j g) :
    ∫⁻ ν : T.G, Γ.positionsOfSize.indicator (F.depthWeight j g) (g⁻¹ * (ν * y))
      ∂ascConv heisenbergMeasure j ≤ ∏ l ∈ Finset.range j, Γ.floorConst l := by
  -- Move both points by the element `γ * n` of `R^(j)` that takes `g` into the box `F.boxSet`,
  -- then use induction on the length.
  have h_meas : MeasurableSet Γ.positionsOfSize := Γ.measurableSet_positionsOfSize
  obtain ⟨ξ, hξ, hg⟩ : ∃ ξ ∈ partialUnitriangularGroup j, ξ * g ∈ F.boxSet := h_near
  obtain ⟨γ, hγ, n, hn, rfl⟩ : ∃ γ ∈ floorGroup j, ∃ n ∈ unipotentBelow j, ξ = γ * n :=
    exists_floorGroup_mul_unipotentBelow hξ
  have h_floors (a : ℕ) (ha : a ≤ 𝔰.ϱ) (y : T.G) :
      ∫⁻ ν, Γ.positionsOfSize.indicator (F.depthWeight a (γ * n * g)) ((γ * n * g)⁻¹ * (ν * y))
        ∂ascConv heisenbergMeasure a ≤ ∏ l ∈ .range a,
          F.floorModulus l * Γ.loss ^ (4600 * 𝔰.n) := by
    induction a generalizing y with
    | zero => simp [depthWeight, ascConv, indicator_apply_le']
    | succ a ih =>
      have h_ne_top : ∏ l ∈ .range a, F.floorModulus l * Γ.loss ^ (4600 * 𝔰.n) ≠ ∞ :=
        prod_ne_top fun l _ ↦ by simp [floorModulus, mul_eq_top, Γ.loss_ne_top]
      rw [prod_range_succ]
      exact Γ.lintegral_depthWeight_succ_le ⟨a, ha⟩ hg h_ne_top (ih (by lia)) y
  have h_left_inv : .dirac n⁻¹ ∗ₘ ascConv heisenbergMeasure j = ascConv heisenbergMeasure j :=
    (ascConv_heisenbergMeasure_invariant (inv_mem hn)).right
  calc
    _ = ∫⁻ ν, Γ.positionsOfSize.indicator (F.depthWeight j g) (g⁻¹ * (n⁻¹ * (γ⁻¹ * ν * γ) * y))
          ∂ascConv heisenbergMeasure j := by
      -- the measure is invariant under `n⁻¹` and under conjugation by `γ`
      conv_lhs => rw [← h_left_inv, lintegral_dirac_mconv,
        lintegral_eq_of_dirac_mconv_eq (ascConv_heisenbergMeasure_dirac_comm γ hγ)]
    _ = ∫⁻ ν, Γ.positionsOfSize.indicator (F.depthWeight j (γ * n * g))
        ((γ * n * g)⁻¹ * (ν * (γ * y))) ∂ascConv heisenbergMeasure j := by
      have h_weight : F.depthWeight j (γ * n * g) = F.depthWeight j g :=
        funext fun z ↦ depthWeight_mul_left hξ
      rw [h_weight]
      simp [mul_assoc]
    _ ≤ ∏ l ∈ .range j, F.floorModulus l * Γ.loss ^ (4600 * 𝔰.n) := h_floors j hj (γ * y)
    _ ≤ _ := by
      -- `Γ.floorConst l` has a further factor `≥ 1` and a larger exponent
      gcongr
      grw [floorConst, ← Γ.one_le_kernelBound, one_pow, mul_one]
      gcongr
      · exact Γ.one_le_loss
      · norm_num

end New.Floors.Gauge

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Set Function FloorGroups Size Place TraceOne PlaceData
  HyperbolicBasis Finset

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Place A] [Fintype ι] [DecidableEq ι] {m j : ℕ} {p : ℕ → Aˣ} {a : Fin 𝔰.ϱ} {T : 𝔰.Form A}
  [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {Γ : Gauge F} {g x y : T.G}

namespace Gauge

/-- One translate bounds the sizes of g and w_p⁻¹ g. Let j ≤ ϱ, let the head p of length j be
adapted (`Γ.IsHead`), and let g and w_p⁻¹ g be near at j (`F.IsNear`: a translate by an element of
`partialUnitriangularGroup j` lies in the box), where w_p = `weylElem j p`. Then for some σ in
`floorGroup j` the entries of σ g have size 60 n² and those of σ w_p⁻¹ g have size 99 n²
(`Γ.HasMatrixSize`), where n = `𝔰.n`. -/
lemma exists_hasMatrixSize_of_isNear (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p) (hg : F.IsNear j g)
    (h_near : F.IsNear j ((weylElem j p)⁻¹ * g)) :
    ∃ σ ∈ floorGroup j,
      Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (σ * g).val.val ∧
      Γ.HasMatrixSize (99 * 𝔰.n ^ 2) (σ * ((weylElem j p)⁻¹ * g)).val.val := by
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup j, ξ * g ∈ F.boxSet := hg
  obtain ⟨σ, hσ, ν, hν, rfl⟩ : ∃ σ ∈ floorGroup j, ∃ ν ∈ unipotentBelow j, ξ = σ * ν :=
    exists_floorGroup_mul_unipotentBelow hξ
  -- Apply `hasMatrixSize_of_isHead` to `σ * g` and `σ * ν * σ⁻¹`; `σ` commutes with `weylElem j p`.
  have h_comm : σ * ((weylElem j p)⁻¹ * g) = (weylElem j p)⁻¹ * (σ * g) :=
    (weylElem_mul_left_comm hσ).right.symm
  have h_conj : σ * ν * σ⁻¹ ∈ T.unipotentBelow j := conj_mem_unipotentBelow hσ hν
  have h_conj_box : σ * ν * σ⁻¹ * (σ * g) ∈ F.boxSet := by simpa using h_box
  rw [← isNear_mul_iff (mem_partialUnitriangularGroup_of_mem_floorGroup hσ), h_comm] at h_near
  refine ⟨σ, hσ, ?_⟩
  rw [h_comm]
  exact hasMatrixSize_of_isHead Γ.hasMatrixSize_boxSet hj h_near
    ⟨unipotentBelow_le_partialUnitriangularGroup h_conj, h_conj_box⟩ hp h_conj

/-- Let the unit c lie in 𝔡_a = `F.stableProducts a x y`, the set of products ⟨e_a, ω⟩ with the
vectors ω that are stable at x and x y, and let c⁻¹ have size 1. Then e_a has a short dual of size 5
for the points x and x y modulo the level `F.levelUnit` (`Γ.HasShortDual`): divide a stable vector
by its product c with e_a. -/
lemma hasShortDual_of_mem_stableProducts {c : Aˣ} (hc : ↑c ∈ F.stableProducts a x y)
    (hc_size : ↑c⁻¹ ∈ Γ.ofSize 1) : Γ.HasShortDual F.levelUnit x (x * y) a 5 := by
  obtain ⟨ω, ⟨h_orth, ω', h_congr, h_close⟩, hω⟩ :
      ∃ ω : 𝔰.BesselIndex → A, F.IsStable a x (x * y) ω ∧ ω (eStar a) = c := hc
  obtain ⟨h_len, h_agree⟩ : x⁻¹.val.val *ᵥ ω ∈ Γ.vecsOfSize 1 ∧
      F.levelUnit⁻¹.val • (x⁻¹.val.val *ᵥ ω - (x * y)⁻¹.val.val *ᵥ ω') ∈ Γ.vecsOfSize 1 :=
    Γ.mem_vecsOfSize_of_mem_closePairs h_close
  refine ⟨c⁻¹.val • ω, h_orth.smul _, by simp [hω], ?_, c⁻¹.val • ω', h_congr.smul _, ?_⟩
  · simpa only [LengthLeAt, mulVec_smul] using
      mem_vecsOfSize_mono (smul_mem_vecsOfSize hc_size h_len)
  · simpa only [mulVec_smul, ← smul_sub, smul_comm F.levelUnit⁻¹.val] using
      mem_vecsOfSize_mono (smul_mem_vecsOfSize hc_size h_agree)

/-- Let u x and v y lie in the box `F.boxSet`, with u, v in the Bessel unipotent group `T.besselU`,
and let (v y - u x) / `F.levelUnit` have size 2 for Γ (`Γ.HasMatrixSize`). Then the lengths read at
x and y differ by at most size 9 modulo the level `F.levelUnit` (`Γ.GaugesDifferLe`): if ω is
orthogonal to all e_b, b < ϱ, and x⁻¹ ω has size i, then (x⁻¹ ω - y⁻¹ ω') / `F.levelUnit` has size
i + 9 for some ω' congruent to ω modulo the e_b. -/
lemma gaugesDifferLe_last_quotient_of_close {u v : T.G} (hu : u ∈ T.besselU) (hv : v ∈ T.besselU)
    (_hx : u * x ∈ F.boxSet) (hy : v * y ∈ F.boxSet)
    (h_close : Γ.HasMatrixSize 2 (F.levelUnit⁻¹.val • ((v * y).val.val - (u * x).val.val))) :
    Γ.GaugesDifferLe F.levelUnit x y 𝔰.ϱ 9 := by
  -- The lift is `v⁻¹ u ω`, and `x⁻¹ ω - y⁻¹ v⁻¹ u ω = (v y)⁻¹ (v y - u x) x⁻¹ ω`.
  intro i ω hω hω_len
  have h_mem : v⁻¹ * u ∈ unipotentBelow 𝔰.ϱ :=
    (unipotentBelow_eq_besselU .refl).ge (mul_mem (inv_mem hv) hu)
  refine ⟨(v⁻¹ * u).val.val *ᵥ ω, hω.congrBelow_mulVec h_mem, ?_⟩
  have h_eq : F.levelUnit⁻¹.val • (x⁻¹.val.val *ᵥ ω - y⁻¹.val.val *ᵥ (v⁻¹ * u).val.val *ᵥ ω) =
      ((v * y)⁻¹.val.val * (F.levelUnit⁻¹.val • ((v * y).val.val - (u * x).val.val))) *ᵥ
        x⁻¹.val.val *ᵥ ω := by
    simp [smul_mulVec, sub_mulVec, mul_sub, sub_mul, mul_assoc, smul_sub]
  rw [h_eq]
  have h_size : Γ.HasMatrixSize 1 (v * y).val.val := Γ.hasMatrixSize_boxSet hy
  exact mem_vecsOfSize_mono ((h_size.inv.mul h_close).mulVec hω_len)

/-- Bounded depths bound the position. Let u x and v x y lie in the box `F.boxSet` for some u, v in
the Bessel unipotent group `T.besselU`, with (v x y - u x) / `F.levelUnit` of size 2, where
`F.levelUnit` is the level. If each set 𝔡_a = `F.stableProducts a x y` contains a unit whose inverse
has size 1, then (y - 1) / `F.levelUnit` has size 99 n (`Γ.HasMatrixSize`), where n = `𝔰.n`. -/
lemma hasMatrixSize_sub_one_of_forall_stableProducts
    (h_pair : ∃ u ∈ T.besselU, ∃ v ∈ T.besselU,
      u * x ∈ F.boxSet ∧
      v * (x * y) ∈ F.boxSet ∧
      Γ.HasMatrixSize 2 (F.levelUnit⁻¹.val • ((v * (x * y)).val.val - (u * x).val.val)))
    (h_unit : ∀ a : Fin 𝔰.ϱ, ∃ c : Aˣ, ↑c ∈ F.stableProducts a x y ∧ ↑c⁻¹ ∈ Γ.ofSize 1) :
    Γ.HasMatrixSize (99 * 𝔰.n) (F.levelUnit⁻¹.val • (y.val.val - 1)) := by
  -- The frame is balanced at both points. Descend from Y^(ϱ) to the whole space.
  obtain ⟨u, hu, v, hv, hx, hy, h_close⟩ := h_pair
  have h_near_x : F.IsNear 𝔰.ϱ x := ⟨u, mem_partialUnitriangularGroup_of_mem_besselU hu, hx⟩
  have h_near_y : F.IsNear 𝔰.ϱ (x * y) := ⟨v, mem_partialUnitriangularGroup_of_mem_besselU hv, hy⟩
  have h_dual (a : Fin 𝔰.ϱ) : Γ.HasShortDual F.levelUnit x (x * y) a 5 := by
    obtain ⟨c, hc, hc_size⟩ : ∃ c : Aˣ, ↑c ∈ F.stableProducts a x y ∧ ↑c⁻¹ ∈ Γ.ofSize 1 := h_unit a
    exact hasShortDual_of_mem_stableProducts hc hc_size
  have h_top : Γ.GaugesDifferLe F.levelUnit x (x * y) 𝔰.ϱ 9 :=
    gaugesDifferLe_last_quotient_of_close hu hv hx hy h_close
  -- Each floor costs `4 * 5 + 12`, and `9 + 32 ϱ` leaves room below `99 n`.
  have h_differ : Γ.GaugesDifferLe F.levelUnit x (x * y) 0 (9 + (4 * 5 + 12) * 𝔰.ϱ) :=
    h_top.on_whole_space_of_hasShortDual F.star_levelUnit Γ.levelUnit_mem_ofSize le_rfl
      (fun a ha ↦ (isBalanced_of_isNear h_near_x ha).inducedLengthLe)
      (fun a ha ↦ (isBalanced_of_isNear h_near_y ha).inducedLengthLe) fun a _ ↦ h_dual a
  exact (h_differ.hasMatrixSize_sub_one F.star_levelUnit).mono

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- Let j ≤ ϱ, let the heads p, q of length j be adapted (`Γ.IsHead`), and let the inverse of the
level `F.levelUnit` have size 1 (`Γ.ofSize 1`). Let x, x y, w_p⁻¹ x and w_q⁻¹ x y be near at j
(`F.IsNear`), where w_p = `weylElem j p` and w_q = `weylElem j q`. Then for a < j the set
𝔡_a = `F.stableProducts a x y` contains a unit c whose inverse has size 10 n, that is, lies in
`Γ.ofSize (10 * 𝔰.n)`. -/
lemma exists_unit_mem_stableProducts_of_isHead {q : ℕ → Aˣ} (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hq : Γ.IsHead j q) (hM : ↑F.levelUnit⁻¹ ∈ Γ.ofSize 1) (hx : F.IsNear j x)
    (hy : F.IsNear j (x * y)) (h_near_x : F.IsNear j ((weylElem j p)⁻¹ * x))
    (h_near_y : F.IsNear j ((weylElem j q)⁻¹ * (x * y))) (ha : a < j) :
    ∃ c : Aˣ, ↑c ∈ F.stableProducts a x y ∧ ↑c⁻¹ ∈ Γ.ofSize (10 * 𝔰.n) := by
  -- At `z = x` and `z = x y` the vector `z⁻¹ e*_a` has size `8 ϱ + 7`, so a small multiple of
  -- `e*_a` is short from both points.
  have h_len {z : T.G} {r : ℕ → Aˣ} (hr : Γ.IsHead j r) (hz : F.IsNear j z)
      (h_near : F.IsNear j ((weylElem j r)⁻¹ * z)) :
      Γ.LengthLeAt z (8 * 𝔰.ϱ + 7) (Pi.single (eStar a) 1) := by
    obtain ⟨s, hs, h_box⟩ : ∃ s ∈ partialUnitriangularGroup j, s * z ∈ F.boxSet := hz
    have h_col : s.val.val *ᵥ Pi.single (eStar a) 1 ∈ Γ.vecsOfSize (8 * 𝔰.ϱ + 1) :=
      dual_mem_vecsOfSize Γ.hasMatrixSize_boxSet hj h_near ⟨hs, h_box⟩ hr ha
    have h_eq : z⁻¹.val.val *ᵥ Pi.single (eStar a) 1 =
        (s * z)⁻¹.val.val *ᵥ s.val.val *ᵥ Pi.single (eStar a) 1 := by
      rw [mulVec_mulVec]
      simp [mul_assoc]
    rw [LengthLeAt, h_eq]
    exact mem_vecsOfSize_mono ((Γ.hasMatrixSize_boxSet h_box).inv.mulVec h_col)
  obtain ⟨c, hc_size, hc⟩ : ∃ c : Aˣ, ↑c⁻¹ ∈ Γ.ofSize (8 * 𝔰.ϱ + 7 + 2) ∧
      ∀ ω₁ ∈ Γ.vecsOfSize (8 * 𝔰.ϱ + 7), ∀ ω₂ ∈ Γ.vecsOfSize (8 * 𝔰.ϱ + 7),
        (c.val • ω₁, c.val • ω₂) ∈ F.closePairs :=
    Γ.exists_unit_smul_mem_closePairs (8 * 𝔰.ϱ + 7) hM
  let ω : 𝔰.BesselIndex → A := c.val • Pi.single (eStar a) 1
  have h_short : F.IsShortFrom x (x * y) ω := by
    simpa only [ω, IsShortFrom, mulVec_smul] using
      hc _ (h_len hp hx h_near_x) _ (h_len hq hy h_near_y)
  have h_orth : IsOrthogonalBelow a ω := fun b hb ↦ by
    have h_ne : b ≠ a := Fin.ne_of_lt hb
    simp [ω, h_ne]
  exact ⟨c, ⟨ω, h_short.isStable h_orth, by simp [ω]⟩, mem_ofSize_mono hc_size⟩

/-- Let j ≤ `𝔰.ϱ` and let the heads p, q of length j be adapted to the gauge S. If j ≠ 0, let the
inverse of the level M = `F.levelUnit` have size 1 for S (`hM`), and let the numbers of size 10
`𝔰.n` for S have size 1 for Γ (`hS`). Let u x and v x y lie in the box `F.boxSet` for some u, v in
the Bessel unipotent group `T.besselU`, with (v x y - u x) / M of size 2. Let w_p⁻¹ x and w_q⁻¹ x y
be near at j (`F.IsNear`), where w_p = `weylElem j p` and w_q = `weylElem j q`. If each
𝔡_a = `F.stableProducts a x y` with a ≥ j contains a unit whose inverse has size 1, then (y - 1) / M
has size 99 `𝔰.n`. Sizes refer to Γ unless S is named. -/
lemma hasMatrixSize_sub_one_of_stableProducts {q : ℕ → Aˣ} (S : Gauge F) (hj : j ≤ 𝔰.ϱ)
    (hp : S.IsHead j p) (hq : S.IsHead j q) (hM : j ≠ 0 → ↑F.levelUnit⁻¹ ∈ S.ofSize 1)
    (hS : j ≠ 0 → S.ofSize (10 * 𝔰.n) ⊆ Γ.ofSize 1)
    (h_pair : ∃ u ∈ T.besselU, ∃ v ∈ T.besselU,
      u * x ∈ F.boxSet ∧
      v * (x * y) ∈ F.boxSet ∧
      Γ.HasMatrixSize 2 (F.levelUnit⁻¹.val • ((v * (x * y)).val.val - (u * x).val.val)))
    (h_near_x : F.IsNear j ((weylElem j p)⁻¹ * x))
    (h_near_y : F.IsNear j ((weylElem j q)⁻¹ * (x * y)))
    (h_unit : ∀ a : Fin 𝔰.ϱ, j ≤ a.val →
      ∃ c : Aˣ, ↑c ∈ F.stableProducts a x y ∧ ↑c⁻¹ ∈ Γ.ofSize 1) :
    Γ.HasMatrixSize (99 * 𝔰.n) (F.levelUnit⁻¹.val • (y.val.val - 1)) := by
  -- Below `j` the heads provide the units, from `j` on the hypothesis `h_unit` does.
  refine hasMatrixSize_sub_one_of_forall_stableProducts h_pair fun a ↦ ?_
  by_cases ha : a < j
  · obtain ⟨u, hu, v, hv, hx, hy, -⟩ := h_pair
    have hj_ne : j ≠ 0 := by lia
    have hx_near : F.IsNear j x := ⟨u, mem_partialUnitriangularGroup_of_mem_besselU hu, hx⟩
    have hy_near : F.IsNear j (x * y) := ⟨v, mem_partialUnitriangularGroup_of_mem_besselU hv, hy⟩
    obtain ⟨c, hc, hc_size⟩ : ∃ c : Aˣ, ↑c ∈ F.stableProducts a x y ∧ ↑c⁻¹ ∈ S.ofSize (10 * 𝔰.n) :=
      S.exists_unit_mem_stableProducts_of_isHead hj hp hq (hM hj_ne) hx_near hy_near h_near_x
        h_near_y ha
    exact ⟨c, hc, hS hj_ne hc_size⟩
  · exact h_unit a (by lia)

end Gauge

end New.Floors
