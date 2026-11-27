import New.Spanning.Frames.OneFrame

/-!
# Two frames: separation and the gains at one position

A weight made of depths separates the two frames. At a fixed position the form then gains from a
frequency, from two different heads, or from a deep vector. Throughout, θ_l is `F.floorMeasure l`,
and w_p is the Weyl element `weylElem j p` of a head `p` of length `j`.

Notions from other files:
* `PlaceData.IsNear`: `g` is near at `j` if `partialUnitriangularGroup j` moves it into the box
  `F.boxSet`.
* `PlaceData.partialCorrelation`, `PlaceData.pivotL1Norm`: the correlation of a kernel from floor
  `j` on, and the integral over floor `j` (the pivot) of the modulus of the correlation from floor
  `j + 1` on.
* `PlaceData.depthWeight`, `PlaceData.weightedSquareSum`: the product of the powers depth^(-s) over
  the first `j` vectors, and the sum over the floors from `j` on of the weighted squared
  correlations.
* `Gauge.weightedSquareProduct`: the product of the second moments `F.weightedSquareIntegral` of the
  two correlations, times a constant that depends on the gauge and on the head `p`.

## Main definitions and results

* `New.Floors.Gauge.sq_lintegral_le_mul_lintegral`,
  `New.Floors.Gauge.sq_lintegral_mul_comp_weylElem_inv_le_of_section`: separating the frames, also
  with a pivot on a section.
* `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_char`: the gain from a frequency.
* `New.Floors.Gauge.partialCorrelation_mul_eq_integral_sectionPoint`,
  `New.Floors.Gauge.formIntegrandL1Norm_sq_le_of_heads`: the phase of the lifts and the gain from
  two heads.
* `New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_le_sum_deepModulus`: the cut at the first deep
  vector.
* `New.Floors.Gauge.pivotL1Norm_sq_le_of_deep`,
  `New.Floors.Gauge.formMajorant_sq_le_of_hasDeepVector`,
  `New.Floors.Gauge.formMajorant_zero_sq_le_of_hasDeepVector`: the gains from a deep vector.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Fintype FloorGroups ComplexConjugate InnerProductSpace
  PlaceData Finset Function RCLike Place

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} {𝔰 : Shape} (j : ℕ)
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} (p q : ℕ → Aˣ) {ξ : Aˣ} {I : Type} [Fintype I]
  (W : T.G → EuclideanSpace ℂ I) (x : T.G) (Γ : Gauge F)

variable {j p q W x}

/-- **Separating the frames.** Let `p` be a head of length j ≤ ϱ with Weyl element
w_p = `weylElem j p`, let `x` be a position and `F.groupMeasure` a Haar measure. Let `B`, `B'` be
measurable, left invariant under `partialUnitriangularGroup j` and zero off the points near at `j`.
Suppose `f(g)² ≤ K · B(g) / wgt(g) · B'(w_p⁻¹ g) / wgt(w_p⁻¹ g)` where `f(g) ≠ 0`, for the weight
`wgt = F.depthWeight j · x`. Then the square of the integral of `f` against
`F.partialGroupMeasure 0 j` is at most `K · D² · ∫ B · ∫ B'`, with `B`, `B'` integrated against the
convolution of the measures of the floors below `j`. Here `D` is the product of the
`F.floorModulus a (p a)⁻¹` over a < j, times `Γ.floorsConst`. -/
theorem Gauge.sq_lintegral_le_mul_lintegral (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure] {f B B' : T.G → ℝ≥0∞} {K : ℝ≥0∞}
    (hB : (partialUnitriangularGroup j).FixesLeft B ∧ ∀ g : T.G, ¬F.IsNear j g → B g = 0)
    (hB' : (partialUnitriangularGroup j).FixesLeft B' ∧ ∀ g : T.G, ¬F.IsNear j g → B' g = 0)
    (hB_meas : Measurable B) (hB'_meas : Measurable B')
    (hf : ∀ g : T.G, f g ≠ 0 → f g ^ 2 ≤ K * (B g / F.depthWeight j g x) *
      (B' ((weylElem j p)⁻¹ * g) / F.depthWeight j ((weylElem j p)⁻¹ * g) x)) :
    (∫⁻ g : T.G, f g ∂F.partialGroupMeasure 0 j) ^ 2 ≤
      K * ((∏ a ∈ range j, F.floorModulus a (p a)⁻¹) * Γ.floorsConst) ^ 2 *
        (∫⁻ g : T.G, B g ∂descConv F.floorMeasure 0 j) *
        ∫⁻ g : T.G, B' g ∂descConv F.floorMeasure 0 j := by
  -- Cauchy–Schwarz with the weights crossed: `B` at `g` is paired with the inverse weight at
  -- `w_p⁻¹ g`, and conversely. Then integrate each inverse weight over the unipotent group.
  let D : ℝ≥0∞ := (∏ a ∈ range j, F.floorModulus a (p a)⁻¹) * Γ.floorsConst
  have h_weight {Φ : T.G → ℝ≥0∞} (hΦ : ∀ g : T.G, ¬F.IsNear j g → Φ g = 0) (g : T.G) :
      Φ g / F.depthWeight j g x = Φ g * F.invDepthWeight j x g := by
    by_cases h_near : F.IsNear j g
    · simp [invDepthWeight, h_near, div_eq_mul_inv]
    · simp [hΦ g h_near]
  have h_cross (g : T.G) : f g ^ 2 ≤ B' ((weylElem j p)⁻¹ * g) * F.invDepthWeight j x g *
      (K * (B g * F.invDepthWeight j x ((weylElem j p)⁻¹ * g))) := by
    by_cases h_zero : f g = 0
    · simp [h_zero]
    refine (hf g h_zero).trans_eq ?_
    rw [h_weight hB.2, h_weight hB'.2]
    ring
  -- In the first integral put `w_p g` for `g`.
  have h_first : ∫⁻ g, B' ((weylElem j p)⁻¹ * g) * F.invDepthWeight j x g ∂F.partialGroupMeasure 0 j
    ≤
      D * ∫⁻ g, B' g ∂descConv F.floorMeasure 0 j := by
    let Φ (g : T.G) : ℝ≥0∞ := B' g * F.invDepthWeight j x (weylElem j p * g)
    have hΦ_inv : (floorGroup j).FixesLeft Φ := by
      simp +contextual [Φ, weylElem_mul_left_comm, hB'.1]
    calc ∫⁻ g, B' ((weylElem j p)⁻¹ * g) * F.invDepthWeight j x g ∂F.partialGroupMeasure 0 j
        = ∫⁻ g, Φ ((weylElem j p)⁻¹ * g) ∂F.partialGroupMeasure 0 j := by simp [Φ]
      _ = ∫⁻ g, Φ g ∂F.partialGroupMeasure 0 j :=
          lintegral_partialGroupMeasure_weylElem_inv_mul p (by fun_prop) hΦ_inv
      _ ≤ D * ∫⁻ g, B' g ∂descConv F.floorMeasure 0 j := by
          rw [partialGroupMeasure_zero_eq]
          exact Γ.lintegral_mul_invDepthWeight_le hj hp hx .refl hB' hB'_meas
  -- In the second, `w_p⁻¹` is the Weyl element of the head `star p`.
  have h_second : ∫⁻ g, B g * F.invDepthWeight j x ((weylElem j p)⁻¹ * g) ∂F.partialGroupMeasure 0 j
    ≤
      D * ∫⁻ g, B g ∂descConv F.floorMeasure 0 j := by
    grw [← weylElem_star, partialGroupMeasure_zero_eq,
      Γ.lintegral_mul_invDepthWeight_le hj hp.star_head hx .refl hB hB_meas]
    simp [D, floorModulus]
  calc (∫⁻ g, f g ∂F.partialGroupMeasure 0 j) ^ 2
      ≤ (∫⁻ g, B' ((weylElem j p)⁻¹ * g) * F.invDepthWeight j x g ∂F.partialGroupMeasure 0 j) *
          ∫⁻ g, K * (B g * F.invDepthWeight j x ((weylElem j p)⁻¹ * g)) ∂F.partialGroupMeasure 0
            j :=
        sq_lintegral_le (by fun_prop) (by fun_prop) h_cross
    _ ≤ (D * ∫⁻ g, B' g ∂descConv F.floorMeasure 0 j) *
          (K * (D * ∫⁻ g, B g ∂descConv F.floorMeasure 0 j)) := by
        grw [lintegral_const_mul _ (by fun_prop), h_first, h_second]
    _ = _ := by ring

/-- The separation of the frames for the weighted squares of the two correlations ⟨W g, W y⟩ and ⟨W
g, W (w_q⁻¹ w_p y)⟩. Let `W` be a cut Bessel function, `p` a head of length j ≤ ϱ, `x` a position
and `F.groupMeasure` a Haar measure. Suppose that, where `f(g) ≠ 0`, the square f(g)² is at most
`K * Γ.floorsConst` times the two sums of weighted squares, at g and at w_p⁻¹ g, each divided by its
weight. Then the square of the integral of `f` against `F.partialGroupMeasure 0 j` is at most `K`
times `Γ.weightedSquareProduct j p q W x`, the product of the second moments
`F.weightedSquareIntegral` of the two correlations and of a constant that depends on `Γ` and `p`. -/
theorem Gauge.sq_lintegral_le_weightedSquareProduct (hk : F.IsCut W) (hj : j ≤ 𝔰.ϱ)
    (hp : Γ.IsHead j p) (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure]
    {f : T.G → ℝ≥0∞} {K : ℝ≥0∞}
    (hf : ∀ g : T.G, f g ≠ 0 → f g ^ 2 ≤ K * Γ.floorsConst *
      (F.weightedSquareSum (frameCorrelation W 1) x j g / F.depthWeight j g x) *
      (F.weightedSquareSum (frameCorrelation W (weylRatio j p q)) x j ((weylElem j p)⁻¹ * g) /
        F.depthWeight j ((weylElem j p)⁻¹ * g) x)) :
    (∫⁻ g : T.G, f g ∂F.partialGroupMeasure 0 j) ^ 2 ≤ K * Γ.weightedSquareProduct j p q W x := by
  let k₁ : T.G → T.G → ℂ := frameCorrelation W 1
  let k₂ : T.G → T.G → ℂ := frameCorrelation W (weylRatio j p q)
  have ker₁ : F.IsPairingKernel j k₁ 1 := Γ.isPairingKernel_frameCorrelation_one hk j
  have ker₂ : F.IsPairingKernel j k₂ (weylRatio j p q) :=
    Γ.isPairingKernel_frameCorrelation hk j p q
  have h_norm : F.weightedSquareIntegral j k₁ x ≤ F.weightedSquareIntegral 0 k₁ x :=
    ker₁.weightedSquareIntegral_le_weightedSquareIntegral_zero hj.step
  calc (∫⁻ g, f g ∂F.partialGroupMeasure 0 j) ^ 2
      ≤ K * Γ.floorsConst * ((∏ a ∈ range j, F.floorModulus a (p a)⁻¹) * Γ.floorsConst) ^ 2 *
          F.weightedSquareIntegral j k₁ x * F.weightedSquareIntegral j k₂ x :=
        Γ.sq_lintegral_le_mul_lintegral hj hp hx (ker₁.fixesLeft_weightedSquareSum_and_eq_zero x)
          (ker₂.fixesLeft_weightedSquareSum_and_eq_zero x) (by fun_prop) (by fun_prop) hf
    _ ≤ K * Γ.weightedSquareProduct j p q W x := by
        grw [h_norm, weightedSquareProduct]
        exact le_of_eq (by ring)

/-- The modulus of the correlation of the kernel `k` above floor `a` at the points `y`, `y x`, cut
to the `y` at which the vector of floor `a` has depth at least `D`. -/
def PlaceData.deepModulus (F : PlaceData ι T m) (x : T.G) (D : ℝ≥0∞) (k : T.G → T.G → ℂ)
    (a : Fin 𝔰.ϱ) :
    T.G → ℝ≥0∞ :=
  {y : T.G | D ≤ F.depth a y x}.indicator fun y : T.G ↦ ‖F.partialCorrelation (a + 1) k y (y * x)‖ₑ

/-- For a pairing kernel `k`, the cut modulus `F.deepModulus x D k a` is measurable. -/
@[fun_prop]
lemma PlaceData.IsPairingKernel.measurable_deepModulus {k : T.G → T.G → ℂ} {d : T.G}
    (hK : F.IsPairingKernel j k d) (D : ℝ≥0∞) (a : Fin 𝔰.ϱ) :
    Measurable (F.deepModulus x D k a) := by
  have h_deep : MeasurableSet {y : T.G | D ≤ F.depth a y x} :=
    measurableSet_le measurable_const (by fun_prop)
  exact Measurable.indicator (by fun_prop) h_deep

/-- **The cut at the first deep vector.** Let `k` be a pairing kernel (`F.IsPairingKernel`), and
suppose that for each `σ` in `floorGroup l` with k(σ g, σ g x) ≠ 0 some vector from floor `l` on has
depth at least `D` at `σ g`. Then `F.pivotL1Norm l k g (g * x)`, the integral over floor `l` of the
modulus of the correlation from floor `l + 1` on, is at most a sum of pieces, one for each floor `a`
with `l ≤ a < ϱ`: the integral of `F.deepModulus x D k a` over the floors from `l` to `a`. -/
theorem PlaceData.IsPairingKernel.pivotL1Norm_le_sum_deepModulus {k : T.G → T.G → ℂ} {d g : T.G}
    {D : ℝ≥0∞} {l : ℕ} (hK : F.IsPairingKernel j k d)
    (h_deep : ∀ σ ∈ floorGroup l, k (σ * g) (σ * (g * x)) ≠ 0 →
      ∃ a : Fin 𝔰.ϱ, l ≤ a ∧ D ≤ F.depth a (σ * g) x) :
    F.pivotL1Norm l k g (g * x) ≤ ∑ a : Fin 𝔰.ϱ with l ≤ a.val,
      ∫⁻ σ : T.G, F.deepModulus x D k a (σ * g) ∂descConv F.floorMeasure l (a - l + 1) := by
  -- Downward induction on `l`: a frame is deep on floor `l`, or its first deep vector comes later.
  induction h_gap : 𝔰.ϱ - l generalizing l g with
  | zero =>
    -- No floor `a` has `l ≤ a`, so the kernel vanishes along the orbit.
    have h_vanish : ¬∃ σ ∈ floorGroup l, k (σ * g) (σ * (g * x)) ≠ 0 := by
      rintro ⟨σ, hσ, h_ne⟩
      obtain ⟨a, hla, -⟩ : ∃ a : Fin 𝔰.ϱ, l ≤ a ∧ D ≤ F.depth a (σ * g) x := h_deep σ hσ h_ne
      lia
    have h_zero : F.pivotL1Norm l k g (g * x) = 0 := by
      by_contra h_ne
      exact h_vanish (exists_ne_zero_of_pivotL1Norm_ne_zero h_ne)
    simp [h_zero]
  | succ i ih =>
    lift l to Fin 𝔰.ϱ using (by lia)
    -- Each piece is an integral over floor `l` of an integral over the floors from `l + 1` to `a`.
    have h_piece (a : Fin 𝔰.ϱ) :
        ∫⁻ σ, F.deepModulus x D k a (σ * g) ∂descConv F.floorMeasure l (a - l + 1) =
          ∫⁻ σ, ∫⁻ τ, F.deepModulus x D k a (τ * (σ * g))
            ∂descConv F.floorMeasure (l + 1) (a - l) ∂F.floorMeasure l := by
      have h_meas : Measurable fun σ : T.G ↦ F.deepModulus x D k a (σ * g) := by fun_prop
      simp only [descConv, lintegral_mconv_symm h_meas, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ ↦ h_piece a, ← lintegral_finsetSum _ (by fun_prop)]
    rw [pivotL1Norm]
    refine lintegral_mono_ae (ae_floorMeasure_mem.mono fun σ hσ ↦ ?_)
    by_cases h_first : D ≤ F.depth l (σ * g) x
    · -- The integrand is the term `a = l` of the sum.
      refine le_trans (le_of_eq ?_) (single_le_sum (fun _ _ ↦ zero_le) (a := l) (by simp))
      simp [descConv, deepModulus, h_first, mul_assoc]
    · -- The depth on floor `l` is the same at all `τ * (σ * g)`, so a later vector is deep.
      have h_later : ∀ τ ∈ floorGroup (l + 1), k (τ * (σ * g)) (τ * (σ * g * x)) ≠ 0 →
          ∃ a : Fin 𝔰.ϱ, l.val + 1 ≤ a ∧ D ≤ F.depth a (τ * (σ * g)) x := by
        intro τ hτ h_ne
        have h_mem : τ * σ ∈ floorGroup l.val := mul_mem (floorGroup_anti l.val.le_succ hτ) hσ
        have h_same : F.depth l (τ * (σ * g)) x = F.depth l (σ * g) x :=
          depth_mul_left (mem_partialUnitriangularGroup_of_mem_floorGroup hτ)
        obtain ⟨a, hla, h_depth⟩ : ∃ a : Fin 𝔰.ϱ, l.val ≤ a ∧ D ≤ F.depth a (τ * (σ * g)) x := by
          simpa only [mul_assoc] using h_deep (τ * σ) h_mem (by simpa only [mul_assoc] using h_ne)
        refine ⟨a, Nat.lt_of_le_of_ne hla fun h_eq ↦ h_first ?_, h_depth⟩
        rwa [← Fin.ext h_eq, h_same] at h_depth
      have h_len (a : Fin 𝔰.ϱ) (ha : l.val + 1 ≤ a) : a.val - (l + 1) + 1 = a - l := by lia
      calc ‖F.partialCorrelation (l + 1) k (σ * g) (σ * (g * x))‖ₑ
          ≤ F.pivotL1Norm (l + 1) k (σ * g) (σ * g * x) := by
            grw [hK.enorm_partialCorrelation_le, mul_assoc]
        _ ≤ ∑ a : Fin 𝔰.ϱ with l.val + 1 ≤ a.val, ∫⁻ τ, F.deepModulus x D k a (τ * (σ * g))
              ∂descConv F.floorMeasure (l + 1) (a - l) :=
            (ih h_later (by lia)).trans_eq
              (Finset.sum_congr rfl fun a ha ↦ by rw [h_len a (mem_filter.1 ha).2])
        _ ≤ ∑ a : Fin 𝔰.ϱ with l.val ≤ a.val, ∫⁻ τ, F.deepModulus x D k a (τ * (σ * g))
              ∂descConv F.floorMeasure (l + 1) (a - l) :=
            sum_le_sum_of_subset (monotone_filter_right _ fun a _ ↦ Nat.le_of_succ_le)

/-- One piece of the cut. Let `Γ` be a gauge with constant Λ = `Γ.loss`, `k` a pairing kernel for
`j` and `d`, `x` a position, `l ≤ a` and `g` a point. The piece is the integral of
`F.deepModulus x ε⁻¹ k a (σ g)` in σ over the floors from `l` to `a`. Its square is at most ε^s
Λ^(10⁴ n ϱ) times the sum `F.weightedSquareSum k x l g` of the weighted squares from floor `l` on,
divided by the weight of length `l` at `g`. Here n = `𝔰.n`, and s = `F.volumeExponent` is the power
of the inverse depths in the weight `F.depthWeight`. -/
lemma Gauge.lintegral_deepModulus_sq_le {x : T.G} (Γ : Gauge F) {k : T.G → T.G → ℂ} {d : T.G}
    {l : ℕ} {a : Fin 𝔰.ϱ} (hK : F.IsPairingKernel j k d) (hx : x ∈ F.positions) (hla : l ≤ a)
    (ε : ℝ≥0∞) (g : T.G) :
    (∫⁻ σ : T.G, F.deepModulus x ε⁻¹ k a (σ * g) ∂descConv F.floorMeasure l (a - l + 1)) ^ 2 ≤
      ε ^ F.volumeExponent * (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ *
        (F.weightedSquareSum k x l g / F.depthWeight l g x) := by
  -- Cauchy–Schwarz against the inverse weight of length `a + 1`, whose integral is bounded by a
  -- power of Λ times `(F.depthWeight l g x)⁻¹`. The gain ε^s comes from `1 ≤ ε * F.depth a y x`,
  -- which holds where the deep modulus is not zero.
  have h_point (y : T.G) : F.deepModulus x ε⁻¹ k a y ^ 2 ≤
      ε ^ F.volumeExponent * F.invDepthWeight (a + 1) x y * F.weightedSquare a k x y := by
    by_cases h_zero : F.deepModulus x ε⁻¹ k a y = 0
    · simp [h_zero]
    obtain ⟨h_depth, h_ne⟩ : ε⁻¹ ≤ F.depth a y x ∧ F.partialCorrelation (a + 1) k y (y * x) ≠
      0 := by
      simpa [deepModulus] using h_zero
    have h_inv : F.invDepthWeight (a + 1) x y = (F.depthWeight (a + 1) y x)⁻¹ := by
      simp [invDepthWeight, hK.isNear_of_partialCorrelation_ne_zero h_ne]
    have h_gain : 1 ≤ ε * F.depth a y x := by
      rwa [ENNReal.inv_le_iff_le_mul (by simp [depth_ne_top]) (by simp [depth_ne_zero])] at h_depth
    calc F.deepModulus x ε⁻¹ k a y ^ 2
        ≤ (ε * F.depth a y x) ^ F.volumeExponent * ‖F.partialCorrelation (a + 1) k y (y * x)‖ₑ ^
          2 := by
          grw [← h_gain]
          simp [deepModulus, h_depth]
      _ = ε ^ F.volumeExponent * F.invDepthWeight (a + 1) x y * F.weightedSquare a k x y := by
          rw [h_inv, mul_pow, ← depthWeight_div_succ, div_eq_mul_inv]
          ring
  -- Write `a = l + i`, so that the integrals run over `i + 1` floors.
  obtain ⟨i, hi⟩ : ∃ i : ℕ, a.val = l + i := Nat.exists_eq_add_of_le hla
  have h_len : a.val - l = i := by lia
  have h_weight : ∫⁻ σ, F.invDepthWeight (a + 1) x (σ * g) ∂descConv F.floorMeasure l (i + 1) ≤
      (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ * (F.depthWeight l g x)⁻¹ := by
    have h_pow : (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ (i + 1) ≤ (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ :=
      pow_le_pow_right₀ (one_le_pow₀ Γ.one_le_loss) (by lia)
    have h_inv : F.invDepthWeight l x g ≤ (F.depthWeight l g x)⁻¹ := Set.indicator_le_self _ _ g
    grw [hi, add_assoc, Γ.lintegral_invDepthWeight_descConv_le hx (by lia), h_pow, h_inv]
  have h_square : ∫⁻ σ, F.weightedSquare a k x (σ * g) ∂descConv F.floorMeasure l (i + 1) ≤
      F.weightedSquareSum k x l g := by
    grw [hi, hK.lintegral_weightedSquare_le_weightedSquareSum (by lia)]
  calc (∫⁻ σ, F.deepModulus x ε⁻¹ k a (σ * g) ∂descConv F.floorMeasure l (a - l + 1)) ^ 2
      ≤ (∫⁻ σ, ε ^ F.volumeExponent * F.invDepthWeight (a + 1) x (σ * g)
            ∂descConv F.floorMeasure l (i + 1)) *
          ∫⁻ σ, F.weightedSquare a k x (σ * g) ∂descConv F.floorMeasure l (i + 1) := by
        rw [h_len]
        exact sq_lintegral_le (by fun_prop) (by fun_prop) fun σ ↦ h_point (σ * g)
    _ ≤ ε ^ F.volumeExponent * ((Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ * (F.depthWeight l g x)⁻¹) *
          F.weightedSquareSum k x l g := by
        grw [lintegral_const_mul _ (by fun_prop), h_weight, h_square]
    _ = _ := by
        rw [div_eq_mul_inv]
        ring

/-- **Gain from a deep vector.** Let `x` be a position and `k` a pairing kernel
(`F.IsPairingKernel`), and suppose that for each `σ` in `floorGroup l` with k(σ g, σ g x) ≠ 0 some
vector from floor `l` on has depth at least `ε⁻¹` at `σ g`. Then the square of `F.pivotL1Norm`, the
integral over floor `l` of the modulus of the correlation from floor `l + 1` on, is at most
`ε ^ F.volumeExponent` times `Γ.floorsConst` times the sum of the weighted squared correlations from
floor `l` on, divided by the weight `F.depthWeight` of length `l`. -/
theorem Gauge.pivotL1Norm_sq_le_of_deep {k : T.G → T.G → ℂ} {d g : T.G} {ε : ℝ≥0∞} {l : ℕ}
    (hK : F.IsPairingKernel j k d) (hx : x ∈ F.positions)
    (h_deep : ∀ σ ∈ floorGroup l, k (σ * g) (σ * (g * x)) ≠ 0 →
      ∃ a : Fin 𝔰.ϱ, l ≤ a ∧ ε⁻¹ ≤ F.depth a (σ * g) x) :
    F.pivotL1Norm l k g (g * x) ^ 2 ≤ ε ^ F.volumeExponent * Γ.floorsConst *
      (F.weightedSquareSum k x l g / F.depthWeight l g x) := by
  -- Cut into at most `𝔰.ϱ` pieces, each at most the square root of `B`.
  let B : ℝ≥0∞ := ε ^ F.volumeExponent * (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ *
    (F.weightedSquareSum k x l g / F.depthWeight l g x)
  have h_piece (a : Fin 𝔰.ϱ) (hla : l ≤ a) :
      ∫⁻ σ, F.deepModulus x ε⁻¹ k a (σ * g) ∂descConv F.floorMeasure l (a - l + 1) ≤
        B ^ (2 : ℝ)⁻¹ :=
    (le_rpow_inv_iff two_pos).2 (mod_cast Γ.lintegral_deepModulus_sq_le hK hx hla ε g)
  have h_sum : F.pivotL1Norm l k g (g * x) ≤ 𝔰.ϱ * B ^ (2 : ℝ)⁻¹ := by
    calc F.pivotL1Norm l k g (g * x)
        ≤ ∑ a : Fin 𝔰.ϱ with l ≤ a.val,
            ∫⁻ σ, F.deepModulus x ε⁻¹ k a (σ * g) ∂descConv F.floorMeasure l (a - l + 1) :=
          hK.pivotL1Norm_le_sum_deepModulus h_deep
      _ ≤ ∑ a : Fin 𝔰.ϱ with l ≤ a.val, B ^ (2 : ℝ)⁻¹ :=
          sum_le_sum fun a ha ↦ h_piece a (mem_filter.1 ha).2
      _ ≤ 𝔰.ϱ * B ^ (2 : ℝ)⁻¹ := by grw [sum_const, nsmul_eq_mul, card_finset_fin_le]
  have h_count : (𝔰.ϱ : ℝ≥0∞) ≤ Γ.loss ^ 𝔰.ϱ := by
    grw [← Γ.two_le_loss]
    exact_mod_cast 𝔰.ϱ.lt_two_pow_self.le
  have h_const : (Γ.loss ^ 𝔰.ϱ) ^ 2 * (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ ≤ Γ.floorsConst := by
    have h_exp : 𝔰.ϱ * 2 + 10 ^ 4 * 𝔰.n * 𝔰.ϱ ≤ 10 ^ 6 * 𝔰.n ^ 3 := by lia
    rw [← pow_mul, ← pow_mul, ← pow_add]
    exact pow_le_pow_right₀ Γ.one_le_loss h_exp
  calc F.pivotL1Norm l k g (g * x) ^ 2
      ≤ (Γ.loss ^ 𝔰.ϱ) ^ 2 * (B ^ (2 : ℝ)⁻¹) ^ 2 := by grw [h_sum, h_count, mul_pow]
    _ = (Γ.loss ^ 𝔰.ϱ) ^ 2 * B := by
        have h_sq : (B ^ (2 : ℝ)⁻¹) ^ 2 = B := rpow_inv_natCast_pow two_ne_zero B
        rw [h_sq]
    _ = ε ^ F.volumeExponent * ((Γ.loss ^ 𝔰.ϱ) ^ 2 * (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ 𝔰.ϱ) *
          (F.weightedSquareSum k x l g / F.depthWeight l g x) := by
        simp only [B]
        ring
    _ ≤ _ := by grw [h_const]

/-- One position, no gain. Let `W` be a cut Bessel function, `p` a head of length j ≤ ϱ, `q` any
sequence of units, `x` a position and `F.groupMeasure` a Haar measure. Let `V` bound the mass of
floor `j`: for every g, the τ with τ g near at j + 1 have `F.floorMeasure j`-measure at most `V`.
Then Cauchy–Schwarz on floor `j` for each of the two factors `F.pivotL1Norm` gives `F.formMajorant
j p q W x ^ 2 ≤ V ^ 2 * Γ.weightedSquareProduct j p q W x`. -/
theorem Gauge.formMajorant_sq_le_of_floorMassLe (hk : F.IsCut W) (hj : j ≤ 𝔰.ϱ)
    (hp : Γ.IsHead j p) (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure] {V : ℝ≥0∞}
    (h_vol : F.FloorMassLe j V 1) :
    F.formMajorant j p q W x ^ 2 ≤ V ^ 2 * Γ.weightedSquareProduct j p q W x := by
  -- Each pivot costs a factor `V`; the constant `Γ.floorsConst ≥ 1` is not needed.
  refine Γ.sq_lintegral_le_weightedSquareProduct hk hj hp hx fun y _ ↦ ?_
  let k₁ : T.G → T.G → ℂ := frameCorrelation W 1
  let k₂ : T.G → T.G → ℂ := frameCorrelation W (weylRatio j p q)
  let z : T.G := (weylElem j p)⁻¹ * y
  have h_pivot {k : T.G → T.G → ℂ} {d : T.G} (hK : F.IsPairingKernel j k d) (g : T.G) :
      F.pivotL1Norm j k g (g * x) ^ 2 ≤
        V * (F.weightedSquareSum k x j g / F.depthWeight j g x) := by
    grw [hK.pivotL1Norm_sq_le_of_floorMassLe_one h_vol, lintegral_partialCorrelation_sq_le hj]
  have h_const : 1 ≤ Γ.floorsConst := one_le_pow₀ Γ.one_le_loss
  calc (F.pivotL1Norm j k₁ y (y * x) * F.pivotL1Norm j k₂ z (z * x)) ^ 2
      ≤ V * (F.weightedSquareSum k₁ x j y / F.depthWeight j y x) *
          (V * (F.weightedSquareSum k₂ x j z / F.depthWeight j z x)) := by
        grw [mul_pow, h_pivot (Γ.isPairingKernel_frameCorrelation_one hk j),
          h_pivot (Γ.isPairingKernel_frameCorrelation hk j p q)]
    _ = V ^ 2 * 1 * (F.weightedSquareSum k₁ x j y / F.depthWeight j y x) *
          (F.weightedSquareSum k₂ x j z / F.depthWeight j z x) := by ring
    _ ≤ _ := by grw [h_const]

/-- Let `W` be a cut Bessel function, `p` a head of length j ≤ ϱ, `q` a second sequence of units,
`x` a position and `F.groupMeasure` a Haar measure. Let `V ≥ 1` bound the mass of floor `j`: for
every g, the τ with τ g near at j + 1 have `F.floorMeasure j`-measure at most `V`. Suppose that
every active point g has a floor a ≥ j with `σ⁻¹ ≤ F.depth a g x`. Then the square of the majorant
`F.formMajorant j p q W x` of the form at `x` is at most `σ ^ F.volumeExponent * V ^ 2` times
`Γ.weightedSquareProduct`, the product of the second moments of the two correlations with its
constants. -/
theorem Gauge.formMajorant_sq_le_of_hasDeepVector (hk : F.IsCut W) (hj : j ≤ 𝔰.ϱ)
    (hp : Γ.IsHead j p) (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure] {σ V : ℝ≥0∞}
    (h_vol : F.FloorMassLe j V 1) (hV : 1 ≤ V) (h_deep : F.HasDeepVector j p q W x σ⁻¹) :
    F.formMajorant j p q W x ^ 2 ≤
      σ ^ F.volumeExponent * V ^ 2 * Γ.weightedSquareProduct j p q W x := by
  -- The second pivot is bounded by the mass `V`, the first by the lemma on a deep vector.
  refine Γ.sq_lintegral_le_weightedSquareProduct hk hj hp hx fun y h_ne ↦ ?_
  have ker₁ : F.IsPairingKernel j (frameCorrelation W 1) 1 :=
    Γ.isPairingKernel_frameCorrelation_one hk j
  have ker₂ : F.IsPairingKernel j (frameCorrelation W (weylRatio j p q)) (weylRatio j p q) :=
    Γ.isPairingKernel_frameCorrelation hk j p q
  grw [mul_pow, ker₂.pivotL1Norm_sq_le_of_floorMassLe_one h_vol,
    lintegral_partialCorrelation_sq_le hj]
  -- The second modulus is not zero, so for some `τ` the function `W` vanishes at neither of the
  -- translates by `τ` of the two points.
  obtain ⟨τ, hτ, hτ_ne⟩ : ∃ τ ∈ floorGroup j, frameCorrelation W (weylRatio j p q)
      (τ * ((weylElem j p)⁻¹ * y)) (τ * ((weylElem j p)⁻¹ * y * x)) ≠ 0 :=
    exists_ne_zero_of_pivotL1Norm_ne_zero (right_ne_zero_of_mul h_ne)
  have h_ne_p : W (τ * ((weylElem j p)⁻¹ * y)) ≠ 0 := fun h ↦ hτ_ne (by simp [h])
  have h_ne_q : W (τ * ((weylElem j q)⁻¹ * (y * x))) ≠ 0 := fun h ↦
    hτ_ne (by simp [weylRatio, weylElem_mul_left_comm hτ, h, mul_assoc])
  -- Hence both points are near at `j` along the whole orbit of `y` under `floorGroup j`.
  have h_near {ρ : T.G} (hρ : ρ ∈ floorGroup j) {r : ℕ → Aˣ} {z : T.G}
      (hz : W (τ * ((weylElem j r)⁻¹ * z)) ≠ 0) : F.IsNear j ((weylElem j r)⁻¹ * (ρ * z)) := by
    refine .of_floorGroup_mul (hk.isNear_of_ne_zero ?_) (div_mem hτ hρ)
    simpa [weylElem_mul_left_comm hρ, div_eq_mul_inv, mul_assoc] using hz
  have h_deep_orbit (ρ : T.G) (hρ : ρ ∈ floorGroup j)
      (h_pair : frameCorrelation W 1 (ρ * y) (ρ * (y * x)) ≠ 0) :
      ∃ a : Fin 𝔰.ϱ, j ≤ a ∧ σ⁻¹ ≤ F.depth a (ρ * y) x := by
    have h_inner : ⟪W (ρ * y), W (ρ * y * x)⟫_ℂ ≠ 0 := by simpa [mul_assoc] using h_pair
    have h_near_q : F.IsNear j ((weylElem j q)⁻¹ * (ρ * y * x)) := by
      simpa only [mul_assoc] using h_near hρ h_ne_q
    exact h_deep (ρ * y) ⟨h_inner, h_near hρ h_ne_p, h_near_q⟩
  grw [Γ.pivotL1Norm_sq_le_of_deep ker₁ hx h_deep_orbit, ← le_self_pow hV two_ne_zero]
  exact le_of_eq (by ring)

/-- Let `W` be a cut Bessel function, `p` a head of length j ≤ ϱ, `x` a position, `F.groupMeasure` a
Haar measure and `V ≥ 1` a bound for the mass of floor `j`. Write w_p = `weylElem j p` and
w_q = `weylElem j q`. Suppose that, if `σ < 1`, every active point g has a floor a ≥ j with
`σ⁻¹ ≤ F.depth a g x`; g is active when ⟨W g, W (g x)⟩ ≠ 0 and w_p⁻¹ g, w_q⁻¹ g x are near at j.
Then the square of the majorant of the form at `x` is at most `σ ^ F.volumeExponent * V ^ 2` times
`Γ.weightedSquareProduct`, the product of the second moments of the two correlations with its
constants. -/
theorem Gauge.formMajorant_sq_le (hk : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure] {σ V : ℝ≥0∞}
    (h_vol : F.FloorMassLe j V 1) (hV : 1 ≤ V)
    (h_deep : σ < 1 → F.HasDeepVector j p q W x σ⁻¹) :
    F.formMajorant j p q W x ^ 2 ≤
      σ ^ F.volumeExponent * V ^ 2 * Γ.weightedSquareProduct j p q W x := by
  rcases lt_or_ge σ 1 with hσ | hσ
  · exact Γ.formMajorant_sq_le_of_hasDeepVector hk hj hp hx h_vol hV (h_deep hσ)
  · grw [Γ.formMajorant_sq_le_of_floorMassLe hk hj hp hx h_vol, ← hσ, one_pow, one_mul]

/-- With no head, both pivots give the same integral: the majorant of floor `0` for the heads `1`,
`1` is the square of the integral `F.pivotL1Norm` over the pivot of the kernel ⟨W y, W y'⟩ at
the points `1`, `x`. -/
lemma PlaceData.formMajorant_zero_eq :
    F.formMajorant 0 1 1 W x = F.pivotL1Norm 0 (frameCorrelation W 1) 1 x ^ 2 := by
  simp [formMajorant, descConv, weylRatio, sq]

/-- One position, no head. Let `W` be a cut Bessel function and `x` a position, and take both
sequences p, q equal to the constant `1`. Suppose every active point g has a floor a with
`σ⁻¹ ≤ F.depth a g x`; at floor `0`, g is active when ⟨W g, W (g x)⟩ ≠ 0. Then
`F.formMajorant 0 1 1 W x ^ 2` is at most `(σ ^ F.volumeExponent) ^ 2` times
`Γ.weightedSquareProduct 0 1 1 W x`, the product of the second moments with its constants. -/
theorem Gauge.formMajorant_zero_sq_le_of_hasDeepVector (hk : F.IsCut W) (hx : x ∈ F.positions)
    {σ : ℝ≥0∞} (h_deep : F.HasDeepVector 0 1 1 W x σ⁻¹) :
    F.formMajorant 0 1 1 W x ^ 2 ≤ (σ ^ F.volumeExponent) ^ 2 * Γ.weightedSquareProduct 0 1 1 W
      x := by
  let k : T.G → T.G → ℂ := frameCorrelation W 1
  -- At floor `0` every point is near, as soon as the box is not empty. So a point is active if
  -- its correlation is not zero.
  have h_near {z : T.G} (y : T.G) (hy : W y ≠ 0) : F.IsNear 0 z := by
    obtain ⟨u, -, hu_box⟩ : ∃ u ∈ T.besselU, u * y ∈ F.boxSet := hk.exists_mul_mem_box hy
    exact ⟨u * y * z⁻¹, by simp, by simpa using hu_box⟩
  have h_deep_orbit (y : T.G) (_ : y ∈ floorGroup 0) (hy : k (y * 1) (y * (1 * x)) ≠ 0) :
      ∃ a : Fin 𝔰.ϱ, 0 ≤ a.val ∧ σ⁻¹ ≤ F.depth a (y * 1) x := by
    have h_pair : ⟪W y, W (y * x)⟫_ℂ ≠ 0 := by simpa [k] using hy
    have h_ne : W y ≠ 0 := fun h ↦ h_pair (by simp [h])
    simpa using h_deep y ⟨h_pair, h_near y h_ne, h_near y h_ne⟩
  -- The gain for one pivot; the weight of length `0` is `1`.
  have h_pivot_le : F.pivotL1Norm 0 k 1 x ^ 2 ≤
      σ ^ F.volumeExponent * Γ.floorsConst * F.weightedSquareSum k x 0 1 := by
    have ker : F.IsPairingKernel 0 k 1 := Γ.isPairingKernel_frameCorrelation_one hk 0
    simpa [depthWeight] using Γ.pivotL1Norm_sq_le_of_deep (l := 0) (g := 1) ker hx h_deep_orbit
  have h_norm : Γ.weightedSquareProduct 0 1 1 W x =
      Γ.floorsConst ^ 3 * F.weightedSquareSum k x 0 1 ^ 2 := by
    simp [k, descConv, weylRatio, Gauge.weightedSquareProduct, PlaceData.weightedSquareIntegral,
      mul_assoc, sq]
  have h_const : Γ.floorsConst ^ 2 ≤ Γ.floorsConst ^ 3 :=
    pow_le_pow_right₀ (one_le_pow₀ Γ.one_le_loss) (by norm_num)
  calc F.formMajorant 0 1 1 W x ^ 2
      = (F.pivotL1Norm 0 k 1 x ^ 2) ^ 2 := by rw [formMajorant_zero_eq]
    _ ≤ (σ ^ F.volumeExponent * Γ.floorsConst * F.weightedSquareSum k x 0 1) ^ 2 := by
        grw [h_pivot_le]
    _ = (σ ^ F.volumeExponent) ^ 2 *
          (Γ.floorsConst ^ 2 * F.weightedSquareSum k x 0 1 ^ 2) := by ring
    _ ≤ _ := by grw [h_norm, h_const]

/-- Let `W` be a cut Bessel function, `p` a head of length j ≤ ϱ, `q` a second sequence of units,
`x` a position and `F.groupMeasure` a Haar measure. Let ψ be the additive character of the place,
and let ψ(ηz) = ψ(ξz) for the unit ξ and all numbers z of size 200 n² (n = `𝔰.n`) in the gauge
(`Γ.ofSize`). Weight the form by ψ(η Z_jj), where Z_jj is the diagonal entry j of the frame Gram
matrix `T.frameGram`. Then the square of its modulus `F.formIntegrandL1Norm j p q W x` is at most
`(P.kernelBound / P.modulus ξ) ^ card F.FreeIndex` times `Γ.weightedSquareProduct`, the product of
the second moments of the two correlations with its constants. -/
theorem Gauge.formIntegrandL1Norm_sq_le_of_char (hk : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure] {η : A}
    (hφ : ∀ z ∈ Γ.ofSize (200 * 𝔰.n ^ 2), ψ (η * z) = ψ (ξ * z)) :
    F.formIntegrandL1Norm j p q W x
        (fun y : T.G ↦ ψ (η * (T.frameGram y).diag ⟨j, Nat.lt_succ_of_le hj⟩)) ^ 2 ≤
      (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex * Γ.weightedSquareProduct j p q W x := by
  -- On the supports the weight is the character of frequency `ξ`, so the inner integral is `f σ`
  -- times the conjugate of a Fourier transform `G` of `f'`. Cauchy–Schwarz in `σ` and the
  -- Plancherel bound of `Gauge.correlation_plancherel` conclude.
  refine Γ.sq_lintegral_le_weightedSquareProduct hk hj hp hx fun g h_ne ↦ ?_
  lift j to Fin 𝔰.n using (by lia)
  grw [← lintegral_partialCorrelation_sq_le hj, ← lintegral_partialCorrelation_sq_le hj]
  have ker₁ : F.IsPairingKernel j (frameCorrelation W 1) 1 :=
    Γ.isPairingKernel_frameCorrelation_one hk j
  have ker₂ : F.IsPairingKernel j (frameCorrelation W (weylRatio j p q)) (weylRatio j p q) :=
    Γ.isPairingKernel_frameCorrelation hk j p q
  let f (σ : T.G) : ℂ := F.partialCorrelation (j + 1) (frameCorrelation W 1) (σ * g) (σ * (g * x))
  let f' (τ : T.G) : ℂ := F.partialCorrelation (j + 1) (frameCorrelation W (weylRatio j p q))
    (τ * ((weylElem j p)⁻¹ * g)) (τ * ((weylElem j p)⁻¹ * (g * x)))
  have h_form : F.formIntegrand j p q W x
      (fun y : T.G ↦ ψ (η * (T.frameGram y).diag ⟨j, Nat.lt_succ_of_le hj⟩)) g =
        ∫ σ, ∫ τ, ψ (η * star (orbitPoint j σ) ⬝ᵥ T.splitGram *ᵥ orbitPoint j τ) *
          (f σ * conj (f' τ)) ∂F.floorMeasure j ∂F.floorMeasure j := by
    -- The Gram entry is rewritten before `simp` distributes the coercion over `σ * τ⁻¹`.
    simp [Matrix.diag, ↓frameGram_eq_form_orbitPoint, formIntegrand, partialCorrelationProduct,
      mul_assoc,
      f, f']
  rw [h_form] at h_ne ⊢
  -- The double integral is not zero, so `g` and `(weylElem j p)⁻¹ * g` are near at `j`, and one
  -- `t` moves both to a bounded size.
  obtain ⟨σ, hσ, τ, hτ, hfσ, hfτ⟩ : ∃ σ ∈ floorGroup j, ∃ τ ∈ floorGroup j, f σ ≠ 0 ∧ f' τ ≠ 0 := by
    by_contra! h_zero
    refine enorm_ne_zero.1 h_ne (integral_eq_zero_of_ae (ae_floorMeasure_mem.mono fun σ hσ ↦
      integral_eq_zero_of_ae (ae_floorMeasure_mem.mono fun τ hτ ↦ ?_)))
    exact mul_eq_zero_of_right _ (by simpa [or_iff_not_imp_left] using h_zero σ hσ τ hτ)
  obtain ⟨t, ht, h_size, h_size'⟩ : ∃ t ∈ floorGroup j,
      Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (t * g).val.val ∧
      Γ.HasMatrixSize (99 * 𝔰.n ^ 2) (t * ((weylElem j p)⁻¹ * g)).val.val :=
    exists_hasMatrixSize_of_isNear hj hp
      ((ker₁.isNear_of_partialCorrelation_ne_zero hfσ).of_floorGroup_mul hσ)
      ((ker₂.isNear_of_partialCorrelation_ne_zero hfτ).of_floorGroup_mul hτ)
  let S : Set T.G := {σ | t.val.val *ᵥ orbitPoint j σ ∈ Γ.vecsOfSize (60 * 𝔰.n ^ 2 + 6)}
  let S' : Set T.G := {τ | t.val.val *ᵥ orbitPoint j τ ∈ Γ.vecsOfSize (99 * 𝔰.n ^ 2 + 6)}
  have h_supp : ∀ᵐ σ ∂F.floorMeasure j, f σ ≠ 0 → σ ∈ S :=
    Γ.correlation_support ht h_size ker₁ (g * x)
  have h_supp' : ∀ᵐ τ ∂F.floorMeasure j, f' τ ≠ 0 → τ ∈ S' :=
    Γ.correlation_support ht h_size' ker₂ ((weylElem j p)⁻¹ * (g * x))
  -- On the supports the Gram entry has size `200 * 𝔰.n ^ 2`, where `hφ` applies.
  have h_char {σ τ : T.G} (hσ : σ ∈ S) (hτ : τ ∈ S') :
      ψ (η * star (orbitPoint j σ) ⬝ᵥ T.splitGram *ᵥ orbitPoint j τ) =
        ψ (ξ * star (t.val.val *ᵥ orbitPoint j σ) ⬝ᵥ
          T.splitGram *ᵥ t.val.val *ᵥ orbitPoint j τ) := by
    rw [← U.form_mulVec_mulVec t]
    exact hφ _ (Γ.mem_ofSize_mono (Γ.dotProduct_mem_ofSize
      (fun a _ ↦ Γ.neg_mem_iff_and_star_mem_iff.2.2 (hσ a))
      (Size.HasMatrixSize.mulVec Γ.splitGram_and_inv_mem.1 hτ)))
  let G (v : 𝔰.BesselIndex → A) : ℂ :=
    ∫ τ, ψ ((-ξ).val * star (v + 0) ⬝ᵥ T.splitGram *ᵥ t *ᵥ orbitPoint j τ) * f' τ
      ∂F.floorMeasure j
  have hG : Measurable G := by
    unfold G f'
    fun_prop
  have h_inner : ∀ᵐ σ ∂F.floorMeasure j,
      ∫ τ, ψ (η * star (orbitPoint j σ) ⬝ᵥ T.splitGram *ᵥ orbitPoint j τ) *
        (f σ * conj (f' τ)) ∂F.floorMeasure j = f σ * conj (G (t *ᵥ orbitPoint j σ)) := by
    filter_upwards [h_supp] with σ hσ
    rw [← integral_conj, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [h_supp'] with τ hτ
    by_cases hfσ : f σ = 0
    · simp [hfσ]
    by_cases hfτ : f' τ = 0
    · simp [hfτ]
    rw [h_char (hσ hfσ) (hτ hfτ)]
    simp [P.ψ.map_neg_eq_inv, inv_eq_conj, mul_left_comm _ (ψ _)]
  have h_const : Γ.loss ^ (99 * 𝔰.n * (60 * 𝔰.n ^ 2 + 6 + 6)) *
      Γ.loss ^ (99 * 𝔰.n * (99 * 𝔰.n ^ 2 + 12)) ≤ Γ.floorsConst := by
    have h_cube : 𝔰.n ≤ 𝔰.n ^ 3 := Nat.le_self_pow three_ne_zero _
    rw [← pow_add]
    exact pow_le_pow_right₀ Γ.one_le_loss (by linarith)
  have h_bound : ∫⁻ σ in S, ‖G (t *ᵥ orbitPoint j σ)‖ₑ ^ 2 ∂F.floorMeasure j ≤
      Γ.floorsConst * (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex *
        ∫⁻ τ, ‖f' τ‖ₑ ^ 2 ∂F.floorMeasure j := by
    calc ∫⁻ σ in S, ‖G (t *ᵥ orbitPoint j σ)‖ₑ ^ 2 ∂F.floorMeasure j
        = ∫⁻ v in Γ.vecsOfSize (60 * 𝔰.n ^ 2 + 6), ‖G v‖ₑ ^ 2 ∂F.floorQuadricMeasure j :=
          (measurePreserving_mulVec_orbitPoint j ht).setLIntegral_comp_preimage
            (f := fun v ↦ ‖G v‖ₑ ^ 2) measurableSet_vecsOfSize (by fun_prop)
      _ ≤ Γ.loss ^ (99 * 𝔰.n * (60 * 𝔰.n ^ 2 + 6 + 6)) * Γ.loss ^ (99 * 𝔰.n * (99 * 𝔰.n ^ 2 + 12)) *
            (P.kernelBound / P.modulus (-ξ).val) ^ card F.FreeIndex *
            ∫⁻ τ, ‖f' τ‖ₑ ^ 2 ∂F.floorMeasure j :=
          Γ.correlation_plancherel ht h_size' ker₂ ((weylElem j p)⁻¹ * (g * x)) (by simp) (-ξ) 0
            (.inr rfl)
      _ ≤ _ := by
          grw [h_const]
          simp
  have h_off : ∀ᵐ σ ∂F.floorMeasure j, σ ∉ S → f σ * conj (G (t *ᵥ orbitPoint j σ)) = 0 :=
    h_supp.mono fun σ hσ h_out ↦ mul_eq_zero_of_left (of_not_not (mt hσ h_out)) _
  rw [integral_congr_ae h_inner, ← setIntegral_eq_integral_of_ae_compl_eq_zero h_off]
  calc ‖∫ σ in S, f σ * conj (G (t *ᵥ orbitPoint j σ)) ∂F.floorMeasure j‖ₑ ^ 2
      ≤ (∫⁻ σ in S, ‖f σ * conj (G (t *ᵥ orbitPoint j σ))‖ₑ ∂F.floorMeasure j) ^ 2 := by
        grw [enorm_integral_le_lintegral_enorm]
    _ ≤ (∫⁻ σ in S, ‖f σ‖ₑ ^ 2 ∂F.floorMeasure j) *
          ∫⁻ σ in S, ‖G (t *ᵥ orbitPoint j σ)‖ₑ ^ 2 ∂F.floorMeasure j :=
        sq_lintegral_le (by fun_prop) (by fun_prop) (by simp [mul_pow])
    _ ≤ (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex * Γ.floorsConst *
          (∫⁻ σ, ‖f σ‖ₑ ^ 2 ∂F.floorMeasure j) * ∫⁻ τ, ‖f' τ‖ₑ ^ 2 ∂F.floorMeasure j := by
        grw [h_bound, setLIntegral_le_lintegral]
        exact le_of_eq (by ring)
    _ = _ := by simp only [f, f', mul_assoc]

/-- Let `t₀`, `t` lie in `floorGroup (a + 1)`, and let the matrices `t₀ n₀ g` and `t n g` have size
`s` in the gauge (all their entries lie in `Γ.ofSize s`). Then the column of `t₀ n₀ (t₀ n)⁻¹ - 1` at
the basis vector `eStar a` has size `2 s + 6`. -/
lemma Gauge.sub_one_mulVec_eStar_mem_vecsOfSize {a : Fin 𝔰.ϱ} {s : ℕ} {t₀ t n₀ n g : T.G}
    (ht₀ : t₀ ∈ floorGroup (a + 1)) (ht : t ∈ floorGroup (a + 1))
    (h_size₀ : Γ.HasMatrixSize s (t₀ * n₀ * g).val.val)
      (h_size : Γ.HasMatrixSize s (t * n * g).val.val) :
    ((t₀ * n₀ * (t₀ * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar a) 1 ∈
      Γ.vecsOfSize (2 * s + 6) := by
  -- The inverses of `t₀` and `t` fix `eStar a`, so the column can be read off
  -- `(t₀ n₀ g) (t n g)⁻¹ - 1`.
  have h_fix (r : T.G) (hr : r ∈ floorGroup (a + 1)) (b : 𝔰.BesselIndex) :
      r.val.val⁻¹ b (eStar a) = if b = eStar a then 1 else 0 := by
    simpa [Matrix.one_apply] using mem_floorGroup.1 (inv_mem hr) b (eStar a) (by simp)
  have h_prod : Γ.HasMatrixSize (s + (s + 4) + 1 + 1)
      ((t₀ * n₀ * g).val.val * (t * n * g)⁻¹.val.val - 1) := (h_size₀.mul h_size.inv).sub .one
  intro c
  have h_col : ((t₀ * n₀ * (t₀ * n)⁻¹).val.val - 1) c (eStar a) ∈
      Γ.ofSize (s + (s + 4) + 1 + 1) := by
    simpa [mul_apply, Matrix.one_apply, h_fix t ht, h_fix t₀ ht₀, mul_assoc] using
      h_prod c (eStar a)
  exact Γ.mem_ofSize_mono (by simpa using h_col)

/-- Parseval's inequality along the last vector of two heads. Let `W` be a cut Bessel function, `p`
a head of length i + 1 ≤ ϱ, `q` a second sequence of units, and
`ξ = (1 / p_i - 1 / q_i) / F.levelUnit` a unit. On the Heisenberg group of floor `i` the characters
of the two points differ by the frequency `-ξ p_i`. Write the correlation for
`frameCorrelation W (weylRatio (i + 1) p q)`. For `n` in this group let `Φ n` vanish unless
`w_p n g` is near at `i + 1`, and be at most `C` times the squared correlation from floor `i + 1` on
at `(n g, n y)`. Then the integral of `Φ` is at most `C` times
`(P.kernelBound / P.modulus ξ) ^ card F.FreeIndex`, `F.floorModulus i (p i)⁻¹`, `Γ.floorsConst` and
the squared L² norm of the correlation on the next floor. -/
lemma Gauge.lintegral_heisenbergMeasure_le_of_heads (hk : F.IsCut W) {i : ℕ} (hi : i + 1 ≤ 𝔰.ϱ)
    (hp : Γ.IsHead (i + 1) p) (hξ : ξ.val = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val))
    (g y : T.G) {Φ : T.G → ℝ≥0∞} {C : ℝ≥0∞}
    (hΦ : ∀ n ∈ floorUnipotent i, Φ n ≠ 0 → F.IsNear (i + 1) (weylElem (i + 1) p * (n * g)) ∧
      Φ n ≤ C * ‖F.partialCorrelation (i + 1) (frameCorrelation W (weylRatio (i + 1) p q))
        (n * g) (n * y)‖ₑ ^ 2) :
    ∫⁻ n : T.G, Φ n ∂heisenbergMeasure i ≤
      C * ((P.kernelBound / P.modulus ξ) ^ card F.FreeIndex * F.floorModulus i (p i)⁻¹ *
        Γ.floorsConst *
        ∫⁻ σ : T.G, ‖F.partialCorrelation (i + 1 + 1) (frameCorrelation W (weylRatio (i + 1) p q))
          (σ * g) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure (i + 1)) := by
  -- Apply Parseval's inequality `Gauge.parseval_heisenbergMeasure_le`, with frequency `-ξ p_i`
  -- and scale `p_i⁻¹`, to the set `S` of the `n` at which both `w_p n g` and `n g` are near.
  lift i to Fin 𝔰.ϱ using hi
  let d : T.G := weylRatio (i + 1) p q
  let k : T.G → T.G → ℂ := frameCorrelation W d
  have ker₂ : F.IsPairingKernel (i + 1) k d := Γ.isPairingKernel_frameCorrelation hk (i + 1) p q
  let S : Set T.G := {n ∈ floorUnipotent i |
    F.IsNear (i + 1) (weylElem (i + 1) p * (n * g)) ∧ F.IsNear (i + 1) (n * g)}
  have h_twist (s : T.G) (hs : s ∈ floorUnipotent i) :
      F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ 1)) =
        (-ξ * p i).val * simpleRootSum s := by
    rw [simpleRootSum_weylRatio_conj i hs le_rfl, ite_eq_left i.val.lt_succ_self, pow_one]
    simp only [Units.val_mul, Units.val_neg, hξ, div_eq_mul_inv]
    linear_combination (F.levelUnit⁻¹.val * simpleRootSum s) * (p i).inv_mul
  have h_supp (n : T.G) (hn : n ∈ floorUnipotent i) (h_ne : Φ n ≠ 0) :
      n ∈ S ∧ Φ n ≤ C * ‖F.partialCorrelation (i + 1) k (n ^ 1 * g) (n * y)‖ₑ ^ 2 := by
    obtain ⟨h_near, h_le⟩ : F.IsNear (i + 1) (weylElem (i + 1) p * (n * g)) ∧
        Φ n ≤ C * ‖F.partialCorrelation (i + 1) k (n * g) (n * y)‖ₑ ^ 2 := hΦ n hn h_ne
    have h_up : F.partialCorrelation (i + 1) k (n * g) (n * y) ≠ 0 :=
      fun h ↦ h_ne (by simpa [h] using h_le)
    exact ⟨⟨hn, h_near, ker₂.isNear_of_partialCorrelation_ne_zero h_up⟩, by rwa [pow_one]⟩
  -- For `n` in `S`, some `t` in `floorGroup (i + 1)` moves `n g` to size `99 n²`, and the entry
  -- `p_i` of the head has size `10 n`.
  have h_move (n : T.G) (hn : n ∈ S) : ∃ t ∈ floorGroup (i + 1),
      Γ.HasMatrixSize (99 * 𝔰.n ^ 2) (t * n * g).val.val := by
    obtain ⟨-, h_weyl, h_near⟩ := hn
    obtain ⟨t, ht, -, h_size⟩ : ∃ t ∈ floorGroup (i + 1),
        Γ.HasMatrixSize (60 * 𝔰.n ^ 2) (t * (weylElem (i + 1) p * (n * g))).val.val ∧
        Γ.HasMatrixSize (99 * 𝔰.n ^ 2) (t * (n * g)).val.val := by
      simpa only [inv_mul_cancel_left] using
        Γ.exists_hasMatrixSize_of_isNear i.isLt hp h_weyl (by simpa using h_near)
    exact ⟨t, ht, by rwa [mul_assoc]⟩
  have h_head (n : T.G) (hn : n ∈ S) : (p i).val ∈ Γ.ofSize (10 * 𝔰.n) := by
    obtain ⟨-, ⟨s, h_box⟩, h_near⟩ := hn
    have h_near' :
        F.IsNear (i + 1) ((weylElem (i + 1) p)⁻¹ * (weylElem (i + 1) p * (n * g))) := by
      simpa using h_near
    exact (Size.head_entries_mem_ofSize Γ.hasMatrixSize_boxSet i.isLt h_near' h_box hp .refl).1
  have h_centre (n₀ : T.G) (hn₀ : n₀ ∈ S) : ∃ t₀ ∈ partialUnitriangularGroup (i + 1) ⊓ floorGroup i,
      ∃ u ∈ unipotentBelow (i + 1), Γ.HasMatrixSize (99 * 𝔰.n ^ 2) (t₀ * u * g).val.val ∧
        ∀ n ∈ S, ∃ v : 𝔰.BesselIndex → A,
          CongrBelow i (((t₀ * n₀ * (t₀ * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar i) 1) v ∧
          (p i)⁻¹⁻¹.val • v ∈ Γ.vecsOfSize (999 * 𝔰.n ^ 2) := by
    obtain ⟨t₀, ht₀, h_size₀⟩ := h_move n₀ hn₀
    obtain ⟨⟨-, hn₀_low⟩, -⟩ := hn₀
    have ht₀_mem : t₀ ∈ partialUnitriangularGroup (i + 1) ⊓ floorGroup i :=
      ⟨mem_partialUnitriangularGroup_of_mem_floorGroup ht₀, floorGroup_anti i.val.le_succ ht₀⟩
    refine ⟨t₀, ht₀_mem, n₀, hn₀_low, h_size₀, fun n hn ↦ ?_⟩
    obtain ⟨t, ht, h_size⟩ := h_move n hn
    -- The column is its own lift; it has size `198 n² + 6`, so `p_i` times it has size `999 n²`.
    let v : 𝔰.BesselIndex → A := ((t₀ * n₀ * (t₀ * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar i) 1
    have hv : v ∈ Γ.vecsOfSize (2 * (99 * 𝔰.n ^ 2) + 6) :=
      Γ.sub_one_mulVec_eStar_mem_vecsOfSize ht₀ ht h_size₀ h_size
    refine ⟨v, fun _ _ ↦ rfl, fun c ↦ ?_⟩
    rw [inv_inv]
    exact Γ.mem_ofSize_mono (Γ.mul_mem_ofSize (h_head n hn) (hv c))
  have h_modulus : P.modulus (↑(-ξ * p i) * ↑(p i)⁻¹) = P.modulus ξ := by simp
  have h_exp : 100 * 𝔰.n * (99 * 𝔰.n ^ 2 + 999 * 𝔰.n ^ 2 + 31) ≤ 10 ^ 6 * 𝔰.n ^ 3 := by
    have h_cube : 𝔰.n ≤ 𝔰.n ^ 3 := Nat.le_self_pow three_ne_zero _
    linarith
  grw [Γ.parseval_heisenbergMeasure_le i (-ξ * p i) (p i)⁻¹ 1 C ker₂ g y h_twist h_supp
    h_centre, h_modulus, pow_le_pow_right₀ Γ.one_le_loss h_exp]

/-- At a point `g` near at `i + 1`, `F.invDepthWeight i x (weylElem i p * ((weylElem (i + 1) p)⁻¹ *
g))` equals `(F.depthWeight i g x)⁻¹`: the inverse weight of length `i` does not see the last factor
of the Weyl element of length `i + 1`. -/
lemma PlaceData.invDepthWeight_weylElem_of_isNear_succ {i : ℕ} {g : T.G}
    (h_near : F.IsNear (i + 1) g) :
    F.invDepthWeight i x (weylElem i p * ((weylElem (i + 1) p)⁻¹ * g)) =
      (F.depthWeight i g x)⁻¹ := by
  have h_mem : (floorWeyl i (p i).val : T.G)⁻¹ ∈ partialUnitriangularGroup i :=
    inv_mem (mem_partialUnitriangularGroup_of_mem_floorGroup floorWeyl_mem_floorGroup)
  rw [weylElem_succ, _root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left,
    invDepthWeight_mul_left h_mem,
    invDepthWeight, Set.indicator_of_mem (s := {z | F.IsNear i z}) (h_near.anti i.le_succ)]

/-- Let `p` be a head of length i + 1 ≤ ϱ with Weyl element w_p = `weylElem (i + 1) p`, let `x` be a
position, `F.groupMeasure` a Haar measure and `wgt_l = F.depthWeight l · x`. Let `φ` be left
invariant under `floorGroup (i + 1)`, and let `B` be left invariant under
`partialUnitriangularGroup (i + 1)` and zero off the points near at `i + 1`. Suppose that the
integral of `φ (n g)²` over the `n` in the Heisenberg group of floor `i` with `w_p n g` near at
`i + 1` is at most `C · B(g) / wgt_(i+1)(g)`. Let `u(g)` be `wgt_(i+1)(g) φ(g)²` times the inverse
depth weight of length `i` at `weylElem i p * g`, cut to the `g` with `w_p g` near. Then the
integral of `u(w_p⁻¹ g)` against `F.partialGroupMeasure 0 (i + 1)` is at most `C · ∫ B` times
`Γ.floorsConst` and the product of the `F.floorModulus a (p a)⁻¹` over a < i, with `B` integrated
against the convolution of the measures of the floors up to `i`. -/
lemma Gauge.lintegral_indicator_le_of_section (hx : x ∈ F.positions)
    [F.groupMeasure.IsHaarMeasure] {i : ℕ} (hi : i + 1 ≤ 𝔰.ϱ) (hp : Γ.IsHead (i + 1) p)
    {φ B u : T.G → ℝ≥0∞} {C : ℝ≥0∞} (hφ_meas : Measurable φ) (hB_meas : Measurable B)
    (hφ : (floorGroup (i + 1)).FixesLeft φ)
    (hB : (partialUnitriangularGroup (i + 1)).FixesLeft B ∧ ∀ g : T.G,
      ¬F.IsNear (i + 1) g → B g = 0)
    (h_section : ∀ g : T.G,
      ∫⁻ n in {n : T.G | F.IsNear (i + 1) (weylElem (i + 1) p * (n * g))}, φ (n * g) ^ 2
          ∂heisenbergMeasure i ≤
        C * (B g / F.depthWeight (i + 1) g x))
    (hu : u = {g : T.G | F.IsNear (i + 1) (weylElem (i + 1) p * g)}.indicator fun g : T.G ↦
      F.depthWeight (i + 1) g x * F.invDepthWeight i x (weylElem i p * g) * φ g ^ 2) :
    ∫⁻ g : T.G, u ((weylElem (i + 1) p)⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1) ≤
      C * ((∏ a ∈ range i, F.floorModulus a (p a)⁻¹) * Γ.floorsConst *
        ∫⁻ g : T.G, B g ∂descConv F.floorMeasure 0 (i + 1)) := by
  let w : T.G := weylElem (i + 1) p
  let r (g : T.G) : ℝ≥0∞ := F.depthWeight (i + 1) g x * F.invDepthWeight i x (weylElem i p * g)
  have hu_meas : Measurable u := by
    rw [hu]
    exact .indicator (by fun_prop) (measurable_const_mul w measurableSet_isNear)
  -- Integrate first over the Heisenberg group of floor `i`, which fixes `r`.
  have h_heisenberg (g : T.G) : ∫⁻ n, u (n * g) ∂heisenbergMeasure i ≤
      C * (B g * F.invDepthWeight i x (weylElem i p * g)) := by
    have h_set : MeasurableSet {n : T.G | F.IsNear (i + 1) (w * (n * g))} :=
      (measurable_mul_const g).const_mul w measurableSet_isNear
    have h_cancel : F.depthWeight (i + 1) g x * (B g / F.depthWeight (i + 1) g x) = B g :=
      ENNReal.mul_div_cancel (by simp) (by simp)
    calc ∫⁻ n, u (n * g) ∂heisenbergMeasure i
        = r g * ∫⁻ n in {n | F.IsNear (i + 1) (w * (n * g))}, φ (n * g) ^ 2
            ∂heisenbergMeasure i := by
          rw [← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator h_set]
          refine lintegral_congr_ae (ae_mem_floorUnipotent.mono fun n ⟨hn_floor, hn_low⟩ ↦ ?_)
          simp [hu, w, r, Set.indicator, weylElem_mul_left_comm hn_floor, invDepthWeight_mul_left,
            unipotentBelow_le_partialUnitriangularGroup hn_low]
      _ ≤ r g * (C * (B g / F.depthWeight (i + 1) g x)) := by grw [h_section g]
      _ = C * (F.depthWeight (i + 1) g x * (B g / F.depthWeight (i + 1) g x) *
            F.invDepthWeight i x (weylElem i p * g)) := by
          simp only [r]
          ring
      _ = _ := by rw [h_cancel]
  have h_inv : (floorGroup (i + 1)).FixesLeft u := by
    intro σ hσ g
    have h_near : F.IsNear (i + 1) (w * (σ * g)) ↔ F.IsNear (i + 1) (w * g) := by
      rw [(weylElem_mul_left_comm hσ).1,
        isNear_mul_iff (mem_partialUnitriangularGroup_of_mem_floorGroup hσ)]
    have h_value : r (σ * g) * φ (σ * g) ^ 2 = r g * φ g ^ 2 := by
      simp [r, weylElem_mul_left_comm, hφ σ hσ, hσ, invDepthWeight_mul_left,
        floorGroup_anti i.le_succ hσ, mem_partialUnitriangularGroup_of_mem_floorGroup]
    by_cases h : F.IsNear (i + 1) (w * g)
    · simp [hu, w, r, h, h_near.2 h, h_value]
    · simp [hu, w, h, mt h_near.1 h]
  have hp_short : Γ.IsHead i p := fun l hl ↦ hp l hl.step
  -- Shift by `w`, integrate over floor `i`, then over the unipotent group of the floors below.
  let ν : Measure T.G := ascConv heisenbergMeasure i ∗ₘ descConv F.floorMeasure 0 (i + 1)
  calc ∫⁻ g, u (w⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1)
      = ∫⁻ g, ∫⁻ n, u (n * g) ∂heisenbergMeasure i ∂ν := by
        rw [lintegral_partialGroupMeasure_weylElem_inv_mul p hu_meas h_inv,
          partialGroupMeasure_zero_eq,
          ascConv_heisenbergMeasure_succ, mconv_assoc, lintegral_mconv_symm hu_meas]
    _ ≤ C * ∫⁻ g, B g * F.invDepthWeight i x (weylElem i p * g) ∂ν := by
        grw [lintegral_mono h_heisenberg, lintegral_const_mul _ (by fun_prop)]
    _ ≤ _ := by grw [Γ.lintegral_mul_invDepthWeight_le (by lia) hp_short hx i.le_succ hB hB_meas]

/-- **Separating the frames when one pivot runs over a section.** Let `p` be a head of length
i + 1 ≤ ϱ with Weyl element w_p = `weylElem (i + 1) p`, let `x` be a position and `F.groupMeasure`
a Haar measure. Let `wgt_i φ₁²` and `B` be left invariant under `partialUnitriangularGroup (i + 1)`
and `φ₂` under `floorGroup (i + 1)`, and let all three vanish off the points near at `i + 1`; here
`wgt_l = F.depthWeight l · x`. Suppose that the integral of `φ₂ (n g)²` over the `n` in the
Heisenberg group of floor `i` with `w_p n g` near at `i + 1` is at most `K` times
`F.floorModulus i (p i)⁻¹ * Γ.floorsConst` times `B(g) / wgt_(i+1)(g)`. Then the square of the
integral of `φ₁(g) φ₂(w_p⁻¹ g)` against `F.partialGroupMeasure 0 (i + 1)` is at most
`K · ∫ wgt_i φ₁² · ∫ B` times `Γ.floorsConst ^ 3` and the square of the product of the
`F.floorModulus a (p a)⁻¹` over a ≤ i. The last two integrals are against the convolution of the
measures of the floors up to `i`. -/
theorem Gauge.sq_lintegral_mul_comp_weylElem_inv_le_of_section (hx : x ∈ F.positions)
    [F.groupMeasure.IsHaarMeasure] {i : ℕ} (hi : i + 1 ≤ 𝔰.ϱ) (hp : Γ.IsHead (i + 1) p)
    {φ₁ φ₂ B : T.G → ℝ≥0∞} {K : ℝ≥0∞} (hφ₁_meas : Measurable φ₁) (hφ₂_meas : Measurable φ₂)
    (hB_meas : Measurable B)
    (hφ₁ : ((partialUnitriangularGroup (i + 1)).FixesLeft
        fun g : T.G ↦ F.depthWeight i g x * φ₁ g ^ 2) ∧
      ∀ g : T.G, ¬F.IsNear (i + 1) g → F.depthWeight i g x * φ₁ g ^ 2 = 0)
    (hφ₂ : (floorGroup (i + 1)).FixesLeft φ₂ ∧ ∀ g : T.G, ¬F.IsNear (i + 1) g → φ₂ g = 0)
    (hB : (partialUnitriangularGroup (i + 1)).FixesLeft B ∧ ∀ g : T.G,
      ¬F.IsNear (i + 1) g → B g = 0)
    (h_section : ∀ g : T.G,
      ∫⁻ n in {n : T.G | F.IsNear (i + 1) (weylElem (i + 1) p * (n * g))}, φ₂ (n * g) ^ 2
          ∂heisenbergMeasure i ≤
        K * F.floorModulus i (p i)⁻¹ * Γ.floorsConst * (B g / F.depthWeight (i + 1) g x)) :
    (∫⁻ g : T.G, φ₁ g * φ₂ ((weylElem (i + 1) p)⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1)) ^ 2 ≤
      K * (∏ a ∈ range (i + 1), F.floorModulus a (p a)⁻¹) ^ 2 * Γ.floorsConst ^ 3 *
        (∫⁻ g : T.G, F.depthWeight i g x * φ₁ g ^ 2 ∂descConv F.floorMeasure 0 (i + 1)) *
        ∫⁻ g : T.G, B g ∂descConv F.floorMeasure 0 (i + 1) := by
  -- Cauchy–Schwarz with the weights crossed: `wgt_i φ₁²` at `g` is paired with the inverse weight
  -- of length `i + 1` at `w⁻¹ g`, and `wgt_(i+1) φ₂²` at `w⁻¹ g` with that of length `i` at `g`.
  obtain ⟨hφ₂_inv, hφ₂_zero⟩ := hφ₂
  let w : T.G := weylElem (i + 1) p
  let r (g : T.G) : ℝ≥0∞ := F.depthWeight (i + 1) g x * F.invDepthWeight i x (weylElem i p * g)
  let u : T.G → ℝ≥0∞ := {g | F.IsNear (i + 1) (w * g)}.indicator fun g ↦ r g * φ₂ g ^ 2
  have hu_meas : Measurable u :=
    .indicator (by fun_prop) (measurable_const_mul w measurableSet_isNear)
  have h_cross (g : T.G) : (φ₁ g * φ₂ (w⁻¹ * g)) ^ 2 ≤
      F.depthWeight i g x * φ₁ g ^ 2 * F.invDepthWeight (i + 1) x (w⁻¹ * g) * u (w⁻¹ * g) := by
    -- Where the left side is not zero, both points are near and the weights cancel.
    rcases em' (F.IsNear (i + 1) g) with h_far | h_near
    · have h_zero : φ₁ g = 0 := by simpa using hφ₁.2 g h_far
      simp [h_zero]
    rcases em' (F.IsNear (i + 1) (w⁻¹ * g)) with h_far' | h_near'
    · simp [hφ₂_zero _ h_far']
    have h_short : F.invDepthWeight i x (weylElem i p * (w⁻¹ * g)) = (F.depthWeight i g x)⁻¹ :=
      invDepthWeight_weylElem_of_isNear_succ h_near
    have h_long : F.invDepthWeight (i + 1) x (w⁻¹ * g) = (F.depthWeight (i + 1) (w⁻¹ * g) x)⁻¹ := by
      simp [invDepthWeight, h_near']
    have h_u : u (w⁻¹ * g) = r (w⁻¹ * g) * φ₂ (w⁻¹ * g) ^ 2 :=
      Set.indicator_of_mem (by simpa using h_near) _
    calc (φ₁ g * φ₂ (w⁻¹ * g)) ^ 2
        = F.depthWeight i g x * (F.depthWeight i g x)⁻¹ *
            (F.depthWeight (i + 1) (w⁻¹ * g) x * (F.depthWeight (i + 1) (w⁻¹ * g) x)⁻¹) *
            (φ₁ g * φ₂ (w⁻¹ * g)) ^ 2 := by simp [ENNReal.mul_inv_cancel]
      _ ≤ _ := by
          simp only [h_long, h_u, r, h_short]
          exact le_of_eq (by ring)
  -- In the first integral, `w⁻¹` is the Weyl element of the head `star p`.
  have h_first : ∫⁻ g, F.depthWeight i g x * φ₁ g ^ 2 * F.invDepthWeight (i + 1) x (w⁻¹ * g)
        ∂F.partialGroupMeasure 0 (i + 1) ≤
      (∏ a ∈ range (i + 1), F.floorModulus a (p a)⁻¹) * Γ.floorsConst *
        ∫⁻ g, F.depthWeight i g x * φ₁ g ^ 2 ∂descConv F.floorMeasure 0 (i + 1) := by
    grw [← weylElem_star, partialGroupMeasure_zero_eq,
      Γ.lintegral_mul_invDepthWeight_le hi hp.star_head hx .refl hφ₁ (by fun_prop)]
    simp [floorModulus]
  have h_second : ∫⁻ g, u (w⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1) ≤
      K * F.floorModulus i (p i)⁻¹ * Γ.floorsConst *
        ((∏ a ∈ range i, F.floorModulus a (p a)⁻¹) * Γ.floorsConst *
          ∫⁻ g, B g ∂descConv F.floorMeasure 0 (i + 1)) :=
    Γ.lintegral_indicator_le_of_section hx hi hp hφ₂_meas hB_meas hφ₂_inv hB h_section rfl
  calc (∫⁻ g, φ₁ g * φ₂ (w⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1)) ^ 2
      ≤ (∫⁻ g, F.depthWeight i g x * φ₁ g ^ 2 * F.invDepthWeight (i + 1) x (w⁻¹ * g)
          ∂F.partialGroupMeasure 0 (i + 1)) * ∫⁻ g, u (w⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1) :=
        sq_lintegral_le (by fun_prop) (by fun_prop) h_cross
    _ ≤ _ := by
        grw [h_first, h_second, prod_range_succ]
        exact le_of_eq (by ring)

/-- The phase of the lifts. Let the place datum `F` have a gauge, let `W` be a cut Bessel function,
`ξ = (1 / p_i - 1 / q_i) / F.levelUnit`, and let `n` lie in the Heisenberg group of floor `i`. Let
`y'` be the point over `n` of the section `⟨e_i, y'⟩ = star p_i`. The correlation from floor `i + 1`
on at `(n g, n g')` is the integral, over the next vector `y = σ⁻¹ e_(i+1)`, of `ψ(-ξ ⟨y', y⟩)`
times the correlation from floor `i + 2` on at `(σ g, σ g')`, which does not depend on `y'`. -/
lemma Gauge.partialCorrelation_mul_eq_integral_sectionPoint (Γ : Gauge F) (hk : F.IsCut W)
    {i : Fin 𝔰.ϱ} (hξ : ξ.val = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val)) {n : T.G}
    (hn : n ∈ floorUnipotent i) (g g' : T.G) :
    F.partialCorrelation (i + 1) (frameCorrelation W (weylRatio (i + 1) p q)) (n * g) (n * g') =
      ∫ σ : T.G, ψ (-ξ.val * star (sectionPoint i (star (p i).val) n) ⬝ᵥ
          T.splitGram *ᵥ orbitPoint i.succ σ) *
        F.partialCorrelation (i + 1 + 1) (frameCorrelation W (weylRatio (i + 1) p q)) (σ * g)
          (σ * g')
          ∂F.floorMeasure (i + 1) := by
  obtain ⟨t, rfl⟩ : ∃ t : ({k : 𝔰.BesselIndex // i + 1 ≤ floorOf k} → A) × skewAdjoint A,
      n = P.heisenbergElem (T := T) i t := exists_eq_heisenbergElem_of_mem hn
  let ω : 𝔰.BesselIndex → A := inclMatrix A Subtype.val *ᵥ t.1
  obtain ⟨μ, hμ⟩ : ∃ μ : A, sectionPoint i (star (p i).val) (P.heisenbergElem (T := T) i t) =
      star (p i).val • (Pi.single (eStar i) 1 - ω + μ • Pi.single (Sum.inl i) 1) :=
    exists_sectionPoint_heisenbergElem_eq (star (p i).val) t
  have h_phase : F.partialCorrelation (i + 1) (frameCorrelation W (weylRatio (i + 1) p q))
      (P.heisenbergElem (T := T) i t * g) (P.heisenbergElem (T := T) i t * g') =
        ∫ σ : T.G, ψ (-(F.levelUnit⁻¹.val * ((p i / q i).val - 1)) *
            star ω ⬝ᵥ T.splitGram *ᵥ orbitPoint i.succ σ) *
          F.partialCorrelation (i + 1 + 1) (frameCorrelation W (weylRatio (i + 1) p q)) (σ * g)
            (σ * g')
            ∂F.floorMeasure (i + 1) := by
    simpa [ω] using partialCorrelation_weylRatio_heisenbergElem i (ε := 1) le_rfl le_rfl
      (Γ.isPairingKernel_frameCorrelation hk (i + 1) p q) t g g'
  rw [h_phase]
  refine integral_congr_ae (ae_floorMeasure_mem.mono fun σ hσ ↦ ?_)
  -- The next vector `y` is orthogonal to `e_i` and `e*_i`, so `⟨y', y⟩ = -p_i ⟨ω, y⟩`.
  have h_orth (k : 𝔰.BesselIndex) (h_lt : floorOf k < i + 1) :
      star (Pi.single k (1 : A)) ⬝ᵥ T.splitGram *ᵥ orbitPoint i.succ σ =
        star (Pi.single k (1 : A)) ⬝ᵥ T.splitGram *ᵥ Pi.single (𝔰.besselFrame i.succ) 1 := by
    have h_fix : (σ.val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ Pi.single k 1 =
        Pi.single k 1 := by
      ext l
      simpa [Pi.single_apply, Matrix.one_apply] using mem_floorGroup.1 hσ l k h_lt
    rw [← U.form_mulVec_mulVec σ, h_fix, orbitPoint_eq_iff.1 rfl]
  have h_floor : floorOf (𝔰.besselFrame i.succ) = i + 1 := floorOf_besselFrame
  have h_e : star (Pi.single (Sum.inl i) (1 : A)) ⬝ᵥ T.splitGram *ᵥ orbitPoint i.succ σ = 0 := by
    have h_ne : eStar i ≠ 𝔰.besselFrame i.succ := fun h ↦ by
      rw [← h] at h_floor
      exact i.val.succ_ne_self h_floor.symm
    rw [h_orth _ (by simp)]
    simp [h_ne]
  have h_dual : star (Pi.single (eStar i) (1 : A)) ⬝ᵥ T.splitGram *ᵥ orbitPoint i.succ σ = 0 := by
    have h_ne : Sum.inl i ≠ 𝔰.besselFrame i.succ := fun h ↦ by simp [← h] at h_floor
    rw [h_orth _ (by simp)]
    simp [h_ne]
  have h_form : star (sectionPoint i (star (p i).val) (P.heisenbergElem (T := T) i t)) ⬝ᵥ
        T.splitGram *ᵥ orbitPoint i.succ σ =
      -(p i).val * star ω ⬝ᵥ T.splitGram *ᵥ orbitPoint i.succ σ := by
    simp only [hμ, star_smul, star_add, star_sub, star_star, smul_dotProduct, add_dotProduct,
      sub_dotProduct, h_e, h_dual, smul_eq_mul]
    ring
  have h_freq : -(F.levelUnit⁻¹.val * ((p i / q i).val - 1)) = -ξ.val * -(p i).val := by
    rw [hξ, div_eq_mul_inv, Units.val_mul]
    linear_combination -F.levelUnit⁻¹.val * (p i).inv_mul
  simp only [h_form, h_freq, mul_assoc]

/-- Plancherel's bound for a pivot on a section. Let `W` be a cut Bessel function, `p` a head of
length `i + 1` and `ξ = (1 / p_i - 1 / q_i) / F.levelUnit`. Let `φ(σ)` be the correlation from floor
`i + 2` on at `(σ g, σ g')`, let `y = orbitPoint i.succ σ`, and let `y'` be the point over `n` of
the section `⟨e_i, y'⟩ = star p_i`. Over the `n` with `w_p n g` near at `i + 1`, the squared L² norm
of `n ↦ ∫ ψ(-ξ ⟨y', y⟩) φ(σ) dθ_(i+1)(σ)` is at most
`(P.kernelBound / P.modulus ξ) ^ card F.FreeIndex` times `F.floorModulus i (p i)⁻¹ * Γ.floorsConst`
times that of `φ`. -/
lemma Gauge.lintegral_section_le (hk : F.IsCut W) {i : Fin 𝔰.ϱ} (hp : Γ.IsHead (i + 1) p)
    (hξ : ξ.val = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val)) (g g' : T.G) :
    ∫⁻ n in {n : T.G | F.IsNear (i + 1) (weylElem (i + 1) p * (n * g))},
        ‖∫ σ : T.G, ψ (-ξ.val * star (sectionPoint i (star (p i).val) n) ⬝ᵥ
            T.splitGram *ᵥ orbitPoint i.succ σ) *
          F.partialCorrelation (i + 1 + 1) (frameCorrelation W (weylRatio (i + 1) p q)) (σ * g)
            (σ * g')
            ∂F.floorMeasure (i + 1)‖ₑ ^ 2 ∂heisenbergMeasure i ≤
      (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex * F.floorModulus i (p i)⁻¹ * Γ.floorsConst *
        ∫⁻ σ : T.G, ‖F.partialCorrelation (i + 1 + 1) (frameCorrelation W (weylRatio (i + 1) p q))
          (σ * g) (σ * g')‖ₑ ^ 2 ∂F.floorMeasure (i + 1) := by
  have h_meas : MeasurableSet {n : T.G | F.IsNear (i + 1) (weylElem (i + 1) p * (n * g))} :=
    ((measurable_mul_const g).const_mul _) measurableSet_isNear
  rw [← lintegral_indicator h_meas]
  refine (Γ.lintegral_heisenbergMeasure_le_of_heads hk i.isLt hp hξ g g' (C := 1)
    fun n hn h_ne ↦ ?_).trans_eq (one_mul _)
  have h_near : n ∈ {n : T.G | F.IsNear (i + 1) (weylElem (i + 1) p * (n * g))} :=
    Set.mem_of_indicator_ne_zero h_ne
  rw [Set.indicator_of_mem h_near, ← Γ.partialCorrelation_mul_eq_integral_sectionPoint hk hξ hn,
    one_mul]
  exact ⟨h_near, le_rfl⟩

/-- Let `W` be a cut Bessel function, `p` a head of length j = i + 1 ≤ ϱ, `q` a second sequence of
units, `x` a position and `F.groupMeasure` a Haar measure, and let
`ξ = (1 / p_i - 1 / q_i) / F.levelUnit` be a unit. Then the square of the L¹ norm
`F.formIntegrandL1Norm j p q W x 1` of the form integrand with weight `1` at `x` is at most
`(P.kernelBound / P.modulus ξ) ^ card F.FreeIndex` times `Γ.weightedSquareProduct j p q W x`, the
product of the second moments of the two correlations with `Γ.floorsConst ^ 3` and the squares of
the `F.floorModulus a (p a)⁻¹` over a < j. -/
theorem Gauge.formIntegrandL1Norm_sq_le_of_heads (hk : F.IsCut W) (hj : j ≤ 𝔰.ϱ) (hp : Γ.IsHead j p)
    (hx : x ∈ F.positions) [F.groupMeasure.IsHaarMeasure] {i : ℕ} (hi : j = i + 1)
    (hξ : ξ.val = F.levelUnit⁻¹.val * ((p i)⁻¹.val - (q i)⁻¹.val)) :
    F.formIntegrandL1Norm j p q W x 1 ^ 2 ≤
      (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex * Γ.weightedSquareProduct j p q W x := by
  -- Separate the frames, with the first pivot `y'` on a section. The second correlation carries
  -- the phase `ψ(-ξ ⟨y', y⟩)`, and Plancherel's formula gives the gain.
  subst hi
  let k₁ : T.G → T.G → ℂ := frameCorrelation W 1
  let k₂ : T.G → T.G → ℂ := frameCorrelation W (weylRatio (i + 1) p q)
  have ker₁ : F.IsPairingKernel i k₁ 1 := Γ.isPairingKernel_frameCorrelation_one hk i
  have ker₂ : F.IsPairingKernel (i + 1) k₂ (weylRatio (i + 1) p q) :=
    Γ.isPairingKernel_frameCorrelation hk (i + 1) p q
  let φ₁ (g : T.G) : ℝ≥0∞ := ‖F.partialCorrelation (i + 1) k₁ g (g * x)‖ₑ
  let φ₂ (g : T.G) : ℝ≥0∞ := ‖F.partialCorrelation (i + 1) k₂ g (g * x)‖ₑ
  have h_form : F.formIntegrandL1Norm (i + 1) p q W x 1 =
      ∫⁻ g, φ₁ g * φ₂ ((weylElem (i + 1) p)⁻¹ * g) ∂F.partialGroupMeasure 0 (i + 1) := by
    simp [formIntegrandL1Norm, ← partialCorrelationProduct_eq Γ hk, partialCorrelationProduct, φ₁,
      φ₂, k₁, k₂]
  have hφ₂ : (floorGroup (i + 1)).FixesLeft φ₂ ∧ ∀ g : T.G, ¬F.IsNear (i + 1) g → φ₂ g = 0 :=
    ⟨fun σ hσ g ↦ by simp [φ₂, ker₂.partialCorrelation_mul_left, hσ, mul_assoc],
      fun g hg ↦ enorm_eq_zero.2 (not_imp_comm.1 ker₂.isNear_of_partialCorrelation_ne_zero hg)⟩
  have h_section (g : T.G) :
      ∫⁻ n in {n | F.IsNear (i + 1) (weylElem (i + 1) p * (n * g))}, φ₂ (n * g) ^ 2
          ∂heisenbergMeasure i ≤
        (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex * F.floorModulus i (p i)⁻¹ *
          Γ.floorsConst *
          (F.weightedSquareSum k₂ x (i + 1) g / F.depthWeight (i + 1) g x) := by
    grw [← lintegral_partialCorrelation_sq_le hj, ← Γ.lintegral_section_le hk (i := ⟨i, hj⟩) hp hξ]
    refine le_of_eq (lintegral_congr_ae (ae_restrict_of_ae (ae_mem_floorUnipotent.mono ?_)))
    intro n hn
    simp only [φ₂, k₂, mul_assoc n]
    rw [Γ.partialCorrelation_mul_eq_integral_sectionPoint hk (i := ⟨i, hj⟩) hξ hn]
  have h_energy : ∫⁻ g, F.weightedSquare i k₁ x g ∂descConv F.floorMeasure 0 (i + 1) ≤
      F.weightedSquareIntegral 0 k₁ x := by
    grw [← ker₁.weightedSquareIntegral_le_weightedSquareIntegral_zero (by lia : i ≤ 𝔰.n),
      ker₁.weightedSquareIntegral_eq_add_succ (by lia),
      ← le_self_add]
  calc F.formIntegrandL1Norm (i + 1) p q W x 1 ^ 2
      ≤ (P.kernelBound / P.modulus ξ) ^ card F.FreeIndex *
          (∏ a ∈ range (i + 1), F.floorModulus a (p a)⁻¹) ^ 2 * Γ.floorsConst ^ 3 *
          (∫⁻ g, F.weightedSquare i k₁ x g ∂descConv F.floorMeasure 0 (i + 1)) *
          ∫⁻ g, F.weightedSquareSum k₂ x (i + 1) g ∂descConv F.floorMeasure 0 (i + 1) := by
        rw [h_form]
        exact Γ.sq_lintegral_mul_comp_weylElem_inv_le_of_section hx hj hp
          (by fun_prop) (by fun_prop) (by fun_prop)
          ker₁.fixesLeft_weightedSquare_and_eq_zero hφ₂
            (ker₂.fixesLeft_weightedSquareSum_and_eq_zero x)
          h_section
    _ ≤ _ := by
        grw [h_energy]
        exact le_of_eq (by simp only [weightedSquareProduct, weightedSquareIntegral, k₁, k₂,
          mul_assoc])

end New.Floors

end
