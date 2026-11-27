import New.Spanning.Frames.Densities

/-!
# One frame

After Cauchy–Schwarz each frame is paired with itself. The square of a partial correlation is
integrated over the position ball along the Heisenberg groups of the frame: a step below the pivot
uses up a weight, a step above it adds a vector by Parseval's formula. The letters G^(l), R^(l),
U_(<l), Y^(l) are those of the head of `New.Spanning.Frames.Lengths`, and K, M those of
`New.Spanning.Frames.Levels`.

## Main definitions and results

* `New.Floors.PlaceData.IsPairingKernel.pivotL1Norm_sq_le`: Cauchy–Schwarz for a pivot whose range
  has small mass.
* `New.Floors.Gauge.lintegral_cutSquare_le`: one step above the pivot.
* `New.Floors.Gauge.lintegral_weightedSquare_le`,
  `New.Floors.Gauge.lintegral_weightedSquareIntegral_le`: the bound for one frame.
* `New.Floors.Gauge.headDensity_mul_lintegral_le_mul_pairingNormSq`: a gain on the position ball
  survives the integration.

Notions from other files:
* `F.floorMeasure l`, written θ_l: the measure of floor l, carried by G^(l) = `floorGroup l`;
  `descConv F.floorMeasure l i` is the convolution θ_{l+i−1} ∗ ⋯ ∗ θ_l.
* `F.IsPairingKernel j k d`: the rules of a correlation k(g, y) = ⟪W g, W (d y)⟫ of a Bessel
  function W, where d commutes with G^(j); `F.partialCorrelation l k`, written k_l, is the average
  of k over the floors from l on.
* `F.depthWeight l g x`, written ℘_l(g, gx): the product of negative powers of the depths of the
  first l frame vectors; `F.weightedSquare l k x g` is ℘_l(g, gx)·|k_{l+1}(g, gx)|².
* `F.weightedSquareSum k x l`, written 𝖻_l: the sum of the integrated weighted squares over the
  floors from l on; `F.weightedSquareIntegral l k x` is its integral over the floors below l.
* `F.IsNear l g`: the coset R^(l) g meets `F.boxSet`, where R^(l) = `partialUnitriangularGroup l`.
-/

namespace New.Floors.PlaceData

open MeasureTheory Measure ProbabilityTheory FloorGroups Set

variable {R ι : Type} {𝔰 : Shape} [CommRing R] [StarRing R] [TopologicalSpace R] [MeasureSpace R]
  [Place R] [Fintype ι] [DecidableEq ι] {m j l : ℕ} {K : ENNReal}
  {T : 𝔰.Form R} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} {x g y : T.G} {k : T.G → T.G → ℂ} {d : T.G}

/-! ### Estimates for pairing kernels -/

/-- If `F.pivotL1Norm l k g y`, the θ_l-integral of |k_{l+1}(σg, σy)|, is not zero, then
k(xg, xy) ≠ 0 for some x in G^(l) = `floorGroup l`. -/
lemma exists_ne_zero_of_pivotL1Norm_ne_zero (h : F.pivotL1Norm l k g y ≠ 0) :
    ∃ x ∈ floorGroup l, k (x * g) (x * y) ≠ 0 := by
  obtain ⟨σ, hσ, h_ne⟩ :
      ∃ σ ∈ floorGroup l, ‖F.partialCorrelation (l + 1) k (σ * g) (σ * y)‖ₑ ≠ 0 :=
    exists_ne_zero_of_ae ae_floorMeasure_mem h
  by_contra! h_zero
  -- Otherwise the integrand of `F.partialCorrelation (l + 1) k (σ * g) (σ * y)` vanishes almost
  -- everywhere, as `x * σ` lies in `floorGroup l`.
  have h_integrand (x : T.G) (hx : x ∈ floorGroup (l + 1)) :
      k (x * (σ * g)) (x * (σ * y)) = 0 := by
    simpa only [mul_assoc] using h_zero (x * σ) (mul_mem (floorGroup_anti l.le_succ hx) hσ)
  exact enorm_ne_zero.1 h_ne
    (integral_eq_zero_of_ae ((ae_descConv_mem ae_floorMeasure_mem).mono h_integrand))

/-- For `l ≤ 𝔰.ϱ`, the integral over σ against θ_l = `F.floorMeasure l` of the squared modulus of
the correlation `F.partialCorrelation (l + 1) k` from floor l + 1 on, taken at (σ g, σ (g x)), is at
most `F.weightedSquareSum k x l g` divided by `F.depthWeight l g x`. -/
lemma lintegral_partialCorrelation_sq_le (hl : l ≤ 𝔰.ϱ) :
    ∫⁻ σ : T.G, ‖F.partialCorrelation (l + 1) k (σ * g) (σ * (g * x))‖ₑ ^ 2 ∂F.floorMeasure l ≤
      F.weightedSquareSum k x l g / F.depthWeight l g x := by
  -- The weight is invariant under `floorGroup l`, so it leaves the integral of `F.weightedSquare`,
  -- a part of `F.weightedSquareSum`.
  have h_ne_zero : F.depthWeight l g x ≠ 0 := by simp
  have h_ne_top : F.depthWeight l g x ≠ ⊤ := by simp
  have h_square : ∀ σ ∈ floorGroup l,
      ‖F.partialCorrelation (l + 1) k (σ * g) (σ * (g * x))‖ₑ ^ 2 * F.depthWeight l g x =
        F.weightedSquare l k x (σ * g) := by
    intro σ hσ
    simp [weightedSquare, mem_partialUnitriangularGroup_of_mem_floorGroup hσ, mul_assoc, mul_comm]
  rw [ENNReal.le_div_iff_mul_le (.inl h_ne_zero) (.inl h_ne_top),
    ← lintegral_mul_const' _ _ h_ne_top, lintegral_floorMeasure_congr rfl h_square]
  grw [weightedSquareSum, ite_eq_left (Nat.lt_succ_of_le hl), ← le_self_add]

namespace IsPairingKernel

/-! ### Weighted squares and their sums over the floors -/

/-- For a pairing kernel `k` at any floor `j`, the sum `F.weightedSquareSum k x l g` of the weighted
squares over the floors from `l` on is jointly measurable in the points `x` and `g` of the group. -/
@[fun_prop]
lemma measurable_weightedSquareSum (hk : F.IsPairingKernel j k d) :
    Measurable ↿(fun x g : T.G ↦ F.weightedSquareSum k x l g) := by
  -- Descending induction on the floor `l`, along the recursion of `weightedSquareSum`; from `𝔰.n`
  -- on the function vanishes. The recursion is run at the points `x = g = 1`, which the statement
  -- does not mention: they only fill the arguments, here and in the induction hypothesis.
  fun_induction F.weightedSquareSum k 1 l 1 with
  | case1 l _ hl ih =>
    have h_succ : Measurable ↿(fun x g : T.G ↦ F.weightedSquareSum k x (l + 1) g) := ih 1
    simp only [weightedSquareSum.eq_1 _ _ _ l, hl, ite_true]
    fun_prop
  | case2 l _ hl =>
    simp only [weightedSquareSum.eq_1 _ _ _ l, hl, ite_false]
    fun_prop

/-- Let `k` be a pairing kernel at floor `j`: it obeys the rules of a correlation ⟪W g, W (d y)⟫,
with `d` commuting with `floorGroup j`. Consider the weighted square `F.weightedSquare j k x`. It is
left invariant under R^(j+1) = `partialUnitriangularGroup (j + 1)`. It vanishes at the points g that
are not near at `j + 1`. -/
lemma fixesLeft_weightedSquare_and_eq_zero (hk : F.IsPairingKernel j k d) :
    (partialUnitriangularGroup (j + 1)).FixesLeft (F.weightedSquare j k x) ∧
    ∀ g : T.G, ¬F.IsNear (j + 1) g → F.weightedSquare j k x g = 0 := by
  refine ⟨fun s hs g ↦ ?_, fun g hg ↦ ?_⟩
  · -- Write `s = γ ν`: weight and kernel are invariant under `γ`; `ν` fixes the weight and
    -- multiplies the kernel by a character value, of modulus one.
    have hs_low : s ∈ partialUnitriangularGroup j := partialUnitriangularGroup_anti le_self_add hs
    obtain ⟨γ, hγ, ν, hν, rfl⟩ : ∃ γ ∈ floorGroup j, ∃ ν ∈ unipotentBelow j, s = γ * ν :=
      exists_floorGroup_mul_unipotentBelow hs_low
    have hγ_up : γ ∈ partialUnitriangularGroup (j + 1) :=
      (mul_mem_cancel_right (unipotentBelow_le_partialUnitriangularGroup hν)).1 hs
    have h_weight : F.depthWeight j (γ * ν * g) x = F.depthWeight j g x := by simp [hs_low]
    have h_norm : ‖F.partialCorrelation (j + 1) k (γ * (ν * g)) (γ * (ν * (g * x)))‖ₑ =
        ‖F.partialCorrelation (j + 1) k g (g * x)‖ₑ := by
      rw [hk.partialCorrelation_mul_left j.le_succ ⟨hγ_up, hγ⟩, hk.equivariance hν hν]
      simp [← ofReal_norm]
    rw [weightedSquare, weightedSquare, h_weight, ← h_norm]
    simp only [mul_assoc]
  · have h_zero : F.partialCorrelation (j + 1) k g (g * x) = 0 :=
      not_imp_comm.1 hk.isNear_of_partialCorrelation_ne_zero hg
    simp [h_zero]

/-- Let `k` be a pairing kernel at floor `j`: it obeys the rules of a correlation ⟪W g, W (d y)⟫,
`d` commuting with `floorGroup j`. The sum 𝖻_j = `F.weightedSquareSum k x j` of the integrated
weighted squares of `k` over the floors from `j` on is left invariant under
R^(j) = `partialUnitriangularGroup j` and vanishes at the points g that are not near at `j`. -/
lemma fixesLeft_weightedSquareSum_and_eq_zero (hk : F.IsPairingKernel j k d) (x : T.G) :
    (partialUnitriangularGroup j).FixesLeft (F.weightedSquareSum k x j) ∧
    ∀ g : T.G, ¬F.IsNear j g → F.weightedSquareSum k x j g = 0 := by
  -- Descending induction on the floor `j`, along the recursion of `weightedSquareSum`; from `𝔰.n`
  -- on the function vanishes. The recursion is run at the point `g = 1`, which the statement does
  -- not mention: it only fills the argument, here and in the induction hypothesis.
  fun_induction F.weightedSquareSum k x j 1 with
  | case2 j _ hj => simp [weightedSquareSum.eq_1 _ _ _ j, hj]
  | case1 j _ hj ih =>
    obtain ⟨h_sum_inv, h_sum_far⟩ :
        (partialUnitriangularGroup (j + 1)).FixesLeft (F.weightedSquareSum k x (j + 1)) ∧
          ∀ g : T.G, ¬F.IsNear (j + 1) g → F.weightedSquareSum k x (j + 1) g = 0 :=
      ih 1 (hk.mono j.le_succ)
    obtain ⟨h_square_inv, h_square_far⟩ :
        (partialUnitriangularGroup (j + 1)).FixesLeft (F.weightedSquare j k x) ∧
          ∀ g : T.G, ¬F.IsNear (j + 1) g → F.weightedSquare j k x g = 0 :=
      hk.fixesLeft_weightedSquare_and_eq_zero
    simp only [Subgroup.FixesLeft, weightedSquareSum.eq_1 _ _ _ j, hj, ite_true]
    refine ⟨fun s hs g ↦ ?_, fun g hg ↦ ?_⟩
    · -- The integrand is invariant under `partialUnitriangularGroup (j + 1)`, so
      -- `lintegral_floorMeasure_mul_right` absorbs `s`.
      have h_inv :
          (partialUnitriangularGroup (j + 1) ⊓ ⊤).FixesLeft fun σ : T.G ↦
            F.weightedSquare j k x (σ * g) + F.weightedSquareSum k x (j + 1) (σ * g) :=
        fun s ⟨hs, _⟩ σ ↦ by simp only [mul_assoc, h_square_inv s hs, h_sum_inv s hs]
      simpa only [mul_assoc] using lintegral_floorMeasure_mul_right le_top h_inv ⟨hs, ⟨⟩⟩
    · -- For `σ` in `floorGroup j` the point `σ g` is not near at `j + 1`, so the integrand
      -- vanishes.
      by_contra h_ne
      obtain ⟨σ, hσ, h_integrand⟩ : ∃ σ ∈ floorGroup j,
          F.weightedSquare j k x (σ * g) + F.weightedSquareSum k x (j + 1) (σ * g) ≠ 0 :=
        exists_ne_zero_of_ae F.ae_floorMeasure_mem h_ne
      have h_far : ¬F.IsNear (j + 1) (σ * g) := fun h_near ↦ hg (h_near.of_floorGroup_mul hσ)
      exact h_integrand (by rw [h_square_far _ h_far, h_sum_far _ h_far, add_zero])

/-- Cauchy–Schwarz on floor `l` for a pairing kernel `k`. Suppose that for every point z the
θ_l-integral of u(σz) over the σ with σz near at `l + 1` is at most `K`, and that ‖k_{l+1}(σg,
σy)‖² ≤ u(σg)·v(σ) for σ in `floorGroup l`, with `u` and `v` measurable. Then the square of
`F.pivotL1Norm l k g y`, the θ_l-integral of ‖k_{l+1}(σg, σy)‖, is at most `K` times the
θ_l-integral of `v`. -/
lemma pivotL1Norm_sq_le (hk : F.IsPairingKernel j k d) {u v : T.G → ENNReal}
    (h_mass : F.FloorMassLe l K u)
    (h_bound : ∀ σ ∈ floorGroup l,
      ‖F.partialCorrelation (l + 1) k (σ * g) (σ * y)‖ₑ ^ 2 ≤ u (σ * g) * v σ)
    (hu : Measurable u := by fun_prop) (hv : Measurable v := by fun_prop) :
    F.pivotL1Norm l k g y ^ 2 ≤ K * ∫⁻ σ : T.G, v σ ∂F.floorMeasure l := by
  classical
  -- `F.floorMeasure l` lives on `floorGroup l`, so the integrand may be cut to that group; the cut
  -- function `f` vanishes outside the set `N` on which `h_mass` bounds the integral of `u`.
  let f : T.G → ENNReal :=
    indicator (T.floorGroup l) fun σ ↦ ‖F.partialCorrelation (l + 1) k (σ * g) (σ * y)‖ₑ
  let N : Set T.G := {σ | F.IsNear (l + 1) (σ * g)}
  have h_supp : f.support ⊆ N := by
    intro σ hσ
    obtain ⟨-, h_ne⟩ := indicator_apply_ne_zero.1 hσ
    exact hk.isNear_of_partialCorrelation_ne_zero (enorm_ne_zero.1 h_ne)
  have h_sq (σ : T.G) : f σ ^ 2 ≤ u (σ * g) * v σ := by
    by_cases hσ : σ ∈ floorGroup l
    · simpa [f, hσ] using h_bound σ hσ
    · simp [f, hσ]
  calc
    F.pivotL1Norm l k g y ^ 2 = (∫⁻ σ in N, f σ ∂F.floorMeasure l) ^ 2 := by
      rw [setLIntegral_eq_of_support_subset h_supp, lintegral_floorMeasure_congr rfl eqOn_indicator,
        pivotL1Norm]
    _ ≤ (∫⁻ σ in N, u (σ * g) ∂F.floorMeasure l) * ∫⁻ σ in N, v σ ∂F.floorMeasure l :=
      sq_lintegral_le (by fun_prop) (by fun_prop) h_sq
    _ ≤ K * ∫⁻ σ, v σ ∂F.floorMeasure l := by grw [h_mass g, setLIntegral_le_lintegral]

/-- Cauchy–Schwarz on floor `l` for a pairing kernel `k`, without a weight: if for every `g` the σ
with σ g near at `l + 1` have θ_l-mass at most `K` (`F.FloorMassLe l K 1`), where
θ_l = `F.floorMeasure l`, then the square of `F.pivotL1Norm l k g y` is at most `K` times the
θ_l-integral of ‖`F.partialCorrelation (l + 1) k (σ * g) (σ * y)`‖². -/
lemma pivotL1Norm_sq_le_of_floorMassLe_one (hk : F.IsPairingKernel j k d)
    (h_mass : F.FloorMassLe l K 1) :
    F.pivotL1Norm l k g y ^ 2 ≤
      K * ∫⁻ σ : T.G, ‖F.partialCorrelation (l + 1) k (σ * g) (σ * y)‖ₑ ^ 2 ∂F.floorMeasure l :=
  hk.pivotL1Norm_sq_le h_mass fun _ _ ↦ (one_mul _).ge

/-- Let `k` be a pairing kernel at any floor `j`, and let `l ≤ 𝔰.ϱ`. Then
`F.weightedSquareIntegral l k x`, the integral of `F.weightedSquareSum k x l` against θ_{l−1} ∗ ⋯ ∗
θ₀, is the integral of the weighted square `F.weightedSquare l k x` against θ_l ∗ ⋯ ∗ θ₀ plus
`F.weightedSquareIntegral (l + 1) k x`. -/
lemma weightedSquareIntegral_eq_add_succ (hk : F.IsPairingKernel j k d) (hl : l ≤ 𝔰.ϱ) :
    F.weightedSquareIntegral l k x =
      ∫⁻ g : T.G, F.weightedSquare l k x g ∂descConv F.floorMeasure 0 (l + 1) +
        F.weightedSquareIntegral (l + 1) k x := by
  -- Split off the last factor `F.floorMeasure l` of `descConv F.floorMeasure 0 (l + 1)`; the inner
  -- integral is `F.weightedSquareSum k x l`.
  rw [weightedSquareIntegral, weightedSquareIntegral, ← lintegral_add_left (by fun_prop),
    descConv_succ, lintegral_mconv_symm (by fun_prop)]
  exact lintegral_congr fun g ↦ by rw [weightedSquareSum, ite_eq_left (Nat.lt_succ_of_le hl)]

/-- For a pairing kernel `k` and `l ≤ 𝔰.n`, `F.weightedSquareIntegral l k x`, the integrated sum of
the weighted squared correlations from floor `l` on, is at most `F.weightedSquareIntegral 0 k x`,
the same quantity taken over all floors. -/
lemma weightedSquareIntegral_le_weightedSquareIntegral_zero (hk : F.IsPairingKernel j k d)
    (hl : l ≤ 𝔰.n) :
    F.weightedSquareIntegral l k x ≤ F.weightedSquareIntegral 0 k x := by
  induction l with
  | zero => rfl
  | succ l ih => grw [← ih (by lia), hk.weightedSquareIntegral_eq_add_succ (l := l) (by lia),
    ← le_add_self]

end IsPairingKernel

end New.Floors.PlaceData

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Fintype FloorGroups ComplexConjugate InnerProductSpace
  PlaceData Finset Function RCLike Place

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ} {𝔰 : Shape} {j : ℕ}
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {p q : ℕ → Aˣ}
  {I : Type} [Fintype I] {W : T.G → EuclideanSpace ℂ I} {x : T.G} (Γ Γ' : Gauge F)

/-! ### Integrals of inverse depth weights and weighted squares over several floors -/

/-- Deep vectors are rare, one floor. Let `Γ` be a gauge for the data `F` of a place, with constant
Λ = `Γ.loss`, let n = `𝔰.n` = ϱ + 1 be the number of floors, each with its measure
`F.floorMeasure a`, and let `x` lie in `F.positions`. The inverse depth weight
`F.invDepthWeight (a + 1) x` at `σ g` has integral over the `σ` of floor `a` at most Λ^(10⁴ n) times
the inverse depth weight of length `a` at `g`. -/
lemma Gauge.lintegral_invDepthWeight_floorMeasure_le {x : T.G} (Γ : Gauge F) (hx : x ∈ F.positions)
    (a : Fin 𝔰.ϱ) (g : T.G) :
    ∫⁻ σ : T.G, F.invDepthWeight (a + 1) x (σ * g) ∂F.floorMeasure a ≤
      Γ.loss ^ (10 ^ 4 * 𝔰.n) * F.invDepthWeight a x g := by
  -- On floor `a` the integrand is `F.invDepthWeight a x g` times the power of the depth, cut to the
  -- near points.
  have h_set : MeasurableSet {σ : T.G | F.IsNear (a + 1) (σ * g)} :=
    measurable_mul_const g measurableSet_isNear
  have h_eq : ∀ σ ∈ floorGroup a.val, F.invDepthWeight (a + 1) x (σ * g) =
      {σ : T.G | F.IsNear (a + 1) (σ * g)}.indicator
        (fun σ : T.G ↦ F.depth a (σ * g) x ^ F.volumeExponent * F.invDepthWeight a x g) σ := by
    intro σ hσ
    by_cases h_near : F.IsNear (a + 1) (σ * g)
    · simp [invDepthWeight, h_near, h_near.of_floorGroup_mul hσ, depthWeight_succ, ENNReal.mul_inv,
        mem_partialUnitriangularGroup_of_mem_floorGroup hσ, depth_ne_zero, depth_ne_top,
          ENNReal.inv_pow,
        mul_comm]
    · simp [invDepthWeight, h_near]
  rw [lintegral_floorMeasure_congr rfl h_eq, lintegral_indicator h_set,
    lintegral_mul_const _ (by fun_prop)]
  grw [Γ.floorMassLe_depth_pow a hx g]

/-- Deep vectors are rare, several floors. Let `Γ` be a gauge for the place datum `F`, with constant
Λ = `Γ.loss`, let n = `𝔰.n` and `l + i ≤ ϱ`, and let `x` lie in `F.positions`. The inverse depth
weight of length `l + i` at `σ g` has integral over the `σ` in the `i` floors from `l` on at most
Λ^(10⁴ n i) times the inverse depth weight of length `l` at `g`. -/
lemma Gauge.lintegral_invDepthWeight_descConv_le {x : T.G} (Γ : Gauge F) (hx : x ∈ F.positions)
    {l i : ℕ} (hi : l + i ≤ 𝔰.ϱ) (g : T.G) :
    ∫⁻ σ : T.G, F.invDepthWeight (l + i) x (σ * g) ∂descConv F.floorMeasure l i ≤
      (Γ.loss ^ (10 ^ 4 * 𝔰.n)) ^ i * F.invDepthWeight l x g := by
  induction i generalizing l g with
  | zero => simp [descConv]
  | succ i ih =>
    let C : ℝ≥0∞ := Γ.loss ^ (10 ^ 4 * 𝔰.n)
    -- Integrate over floor `l` last, and apply the bound for the floors from `l + 1` on.
    calc ∫⁻ σ, F.invDepthWeight (l + (i + 1)) x (σ * g) ∂descConv F.floorMeasure l (i + 1)
        = ∫⁻ τ, ∫⁻ σ, F.invDepthWeight (l + 1 + i) x (σ * (τ * g))
            ∂descConv F.floorMeasure (l + 1) i ∂F.floorMeasure l := by
          rw [descConv, lintegral_mconv_symm (by fun_prop)]
          simp only [mul_assoc, add_assoc, add_comm 1 i]
      _ ≤ ∫⁻ τ, C ^ i * F.invDepthWeight (l + 1) x (τ * g) ∂F.floorMeasure l :=
          lintegral_mono fun τ ↦ ih (by lia) (τ * g)
      _ ≤ C ^ i * (C * F.invDepthWeight l x g) := by
          rw [lintegral_const_mul _ (by fun_prop)]
          grw [Γ.lintegral_invDepthWeight_floorMeasure_le hx ⟨l, by lia⟩]
      _ = C ^ (i + 1) * F.invDepthWeight l x g := by rw [pow_succ, mul_assoc]

/-- Let `k` be a pairing kernel at any floor `j`, `x` any point of the group and `l + i ≤ ϱ`. The
weighted square of floor `l + i`, taken at the pair `σ g`, `σ g x`, has integral over `σ` against
the convolution of the measures of the floors from `l` to `l + i` at most
`F.weightedSquareSum k x l g`, of which it is one term once the recursion is unfolded. -/
lemma PlaceData.IsPairingKernel.lintegral_weightedSquare_le_weightedSquareSum {x : T.G}
    {k : T.G → T.G → ℂ} {d : T.G} (hK : F.IsPairingKernel j k d) {l i : ℕ} (hi : l + i ≤ 𝔰.ϱ)
    (g : T.G) :
    ∫⁻ σ : T.G, F.weightedSquare (l + i) k x (σ * g) ∂descConv F.floorMeasure l (i + 1) ≤
      F.weightedSquareSum k x l g := by
  induction i generalizing l g with
  | zero =>
    grw [weightedSquareSum, ite_eq_left (by lia), ← le_self_add]
    simp [descConv]
  | succ i ih =>
    calc ∫⁻ σ, F.weightedSquare (l + (i + 1)) k x (σ * g) ∂descConv F.floorMeasure l (i + 1 + 1)
        = ∫⁻ τ, ∫⁻ σ, F.weightedSquare (l + 1 + i) k x (σ * (τ * g))
            ∂descConv F.floorMeasure (l + 1) (i + 1) ∂F.floorMeasure l := by
          rw [descConv, lintegral_mconv_symm (by fun_prop)]
          simp only [mul_assoc, add_assoc, add_comm 1 i]
      _ ≤ ∫⁻ τ, F.weightedSquareSum k x (l + 1) (τ * g) ∂F.floorMeasure l :=
          lintegral_mono fun τ ↦ ih (by lia) (τ * g)
      _ ≤ F.weightedSquareSum k x l g := by
          conv_rhs => rw [weightedSquareSum, ite_eq_left (by lia)]
          exact lintegral_mono fun τ ↦ le_add_self

/-- Let μ be a measure on the group, in the variable x, let j ≤ ϱ and let k be a pairing kernel at
floor j. If for every floor l with `j ≤ l ≤ 𝔰.ϱ` the integral of the weighted square of floor l,
over g against the convolution θ_l ∗ ⋯ ∗ θ₀ of the floor measures and over x against μ, is at most
`c`, then the weighted square integral `F.weightedSquareIntegral j k x` has μ-integral at most
`𝔰.n * c`. -/
theorem lintegral_weightedSquareIntegral_le_of_lintegral_le {k : T.G → T.G → ℂ} {d : T.G} {c : ℝ≥0∞}
    {μ : Measure T.G} (hK : F.IsPairingKernel j k d) (hj : j ≤ 𝔰.ϱ)
    (h_term : ∀ {l : ℕ}, j ≤ l → l ≤ 𝔰.ϱ →
      ∫⁻ x : T.G, ∫⁻ g : T.G, F.weightedSquare l k x g ∂descConv F.floorMeasure 0 (l + 1) ∂μ ≤ c) :
    ∫⁻ x : T.G, F.weightedSquareIntegral j k x ∂μ ≤ 𝔰.n * c := by
  -- Add up the terms, from the top floor down to floor `j`.
  have h_partial (l : ℕ) (hjl : j ≤ l) (hl : l ≤ 𝔰.ϱ + 1) :
      l * c + ∫⁻ x, F.weightedSquareIntegral l k x ∂μ ≤ 𝔰.n * c := by
    induction hl using Nat.decreasingInduction with
    | self => simp [weightedSquareIntegral, weightedSquareSum]
    | of_succ l hl ih =>
      have hl' : l ≤ 𝔰.ϱ := by lia
      calc l * c + ∫⁻ x, F.weightedSquareIntegral l k x ∂μ
          ≤ l * c + (c + ∫⁻ x, F.weightedSquareIntegral (l + 1) k x ∂μ) := by
            simp only [hK.weightedSquareIntegral_eq_add_succ hl']
            grw [lintegral_add_left (by fun_prop), h_term hjl hl']
        _ = (l + 1 : ℕ) * c + ∫⁻ x, F.weightedSquareIntegral (l + 1) k x ∂μ := by
            rw [Nat.cast_succ, add_one_mul, add_assoc]
        _ ≤ 𝔰.n * c := ih (by lia)
  exact le_add_self.trans (h_partial j le_rfl hj.step)

/-! ### The bound for one frame -/

/-- For a pairing kernel `k`, the modulus of the correlation `F.partialCorrelation (l + 1) k` above
floor `l` does not change when its second point is multiplied on the left by an element `n` of
`unipotentBelow l`, the unipotent group of the first `l` floors. -/
lemma PlaceData.IsPairingKernel.enorm_partialCorrelation_mul_of_mem_unipotentBelow
    {k : T.G → T.G → ℂ} {d n : T.G} {l : ℕ}
    (hK : F.IsPairingKernel j k d) (hn : n ∈ unipotentBelow l) (g y : T.G) :
    ‖F.partialCorrelation (l + 1) k g (n * y)‖ₑ = ‖F.partialCorrelation (l + 1) k g y‖ₑ := by
  -- The two correlations differ by a value of `ψ`, which has modulus `1`.
  have h_law : F.partialCorrelation (l + 1) k (1 * g) (n * y) =
      ψ (F.levelUnit⁻¹.val * (simpleRootSum (d * n * d⁻¹) - simpleRootSum 1)) *
        F.partialCorrelation (l + 1) k g y :=
    hK.equivariance (one_mem _) hn g y
  rw [one_mul] at h_law
  simp [h_law, ← ofReal_norm]

/-- The measure of the `ν` in the unipotent group of the first `l` floors for which `g⁻¹ ν y` lies
in the position ball. -/
def Gauge.closeMass (l : ℕ) (g y : T.G) : ℝ≥0∞ :=
  ∫⁻ ν : T.G, Γ.positionsOfSize.indicator 1 (g⁻¹ * (ν * y)) ∂ascConv heisenbergMeasure l

/-- The squared modulus of the correlation above floor `l`, cut to the pairs `(g, y)` for which the
positions `g⁻¹ ν y` in the position ball have positive measure: `∞ * m` is `0` for `m = 0` and `∞`
otherwise, so the minimum is `0` or the square. Such a `y` lies in `Γ.closeBelow l g`; the cut takes
the place of the indicator of that set because it is measurable in the pair. -/
def Gauge.cutSquare (k : T.G → T.G → ℂ) (l : ℕ) (g y : T.G) : ℝ≥0∞ :=
  (∞ * Γ.closeMass l g y) ⊓ ‖F.partialCorrelation (l + 1) k g y‖ₑ ^ 2

/-- The cost of one step up from floor `l`: `Γ.floorConst l` below the top floor, and `1` on the top
floor, where only the group H is left, of mass at most `1` on near points. -/
def Gauge.climbConst (l : ℕ) : ℝ≥0∞ := if l < 𝔰.ϱ then Γ.floorConst l else 1

/-- If translating the Haar measure of the unipotent group of the first `l` floors by `σ` on the
left is the same as translating it by `t` on the right, then moving `g`, `y` to `σ g`, `t y` does
not change the mass of the position ball. -/
lemma Gauge.closeMass_mul_mul {l : ℕ} {g y σ t : T.G}
    (h : dirac σ ∗ₘ ascConv heisenbergMeasure l = ascConv heisenbergMeasure l ∗ₘ dirac t) :
    Γ.closeMass l (σ * g) (t * y) = Γ.closeMass l g y := by
  -- Substitute `ν ↦ σ⁻¹ ν t` in the integral on the right.
  have h_subst : Γ.closeMass l g y =
      ∫⁻ ν : T.G, Γ.positionsOfSize.indicator 1 (g⁻¹ * (σ⁻¹ * ν * t * y))
        ∂ascConv heisenbergMeasure l :=
    lintegral_eq_of_dirac_mconv_eq h
  rw [h_subst]
  simp [closeMass, mul_assoc]

/-- For a pairing kernel `k`, the cut square of floor `l` is jointly measurable in its two
points. -/
@[fun_prop]
lemma Gauge.measurable_cutSquare {k : T.G → T.G → ℂ} {d : T.G} (hK : F.IsPairingKernel j k d)
    (l : ℕ) : Measurable ↿(Γ.cutSquare k l) := by
  have hB : MeasurableSet Γ.positionsOfSize := Γ.measurableSet_positionsOfSize
  unfold cutSquare closeMass
  fun_prop

/-- Let `g` be near at `a + 1`. Let `n₀` lie in the Heisenberg group `floorUnipotent a` and `ν₀` in
`unipotentBelow a`, and let `g⁻¹ ν₀ n₀ y` lie in the position ball `Γ.positionsOfSize`. Then there
are `t` in `partialUnitriangularGroup (a + 1) ⊓ floorGroup a` and `ν` in `unipotentBelow (a + 1)`
with two properties. First, the matrix `t ν g` has size 1 for the gauge `Γ`. Second, for each `n` in
the Heisenberg group with `n y` in `Γ.closeBelow a g`, some vector `v` differs from (t n₀ (t n)⁻¹ -
1) e*_a by a combination of the e_b, b < a (`CongrBelow`), and has size 17 after division by the
level unit `F.levelUnit`. -/
lemma Gauge.exists_centre_of_isNear (Γ : Gauge F) (a : Fin 𝔰.ϱ) {g y n₀ ν₀ : T.G}
    (h_near : F.IsNear (a + 1) g) (hn₀ : n₀ ∈ floorUnipotent a) (hν₀ : ν₀ ∈ unipotentBelow a)
    (hy₀ : g⁻¹ * (ν₀ * (n₀ * y)) ∈ Γ.positionsOfSize) :
    ∃ t ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a, ∃ ν ∈ unipotentBelow (a + 1),
      Γ.HasMatrixSize 1 (t * ν * g).val.val ∧
      ∀ n ∈ floorUnipotent a, n * y ∈ Γ.closeBelow a g → ∃ v : 𝔰.BesselIndex → A,
        CongrBelow a (((t * n₀ * (t * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
        F.levelUnit⁻¹.val • v ∈ Γ.vecsOfSize 17 := by
  -- Write the element `ξ` that moves `g` into the box as `t * ν`. The point `t ν ν₀ n₀ y` is close
  -- to `ξ g`, and its translate by `t n (t n₀)⁻¹` lies in `Γ.closeBelow a (ξ g)`.
  obtain ⟨ξ, hξ, h_box⟩ := h_near
  obtain ⟨t, ht, ν, hν, rfl⟩ : ∃ t ∈ floorGroup a, ∃ ν ∈ unipotentBelow a, ξ = t * ν :=
    exists_floorGroup_mul_unipotentBelow (partialUnitriangularGroup_anti a.val.le_succ hξ)
  have ht_mem : t ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a :=
    ⟨(mul_mem_cancel_right (unipotentBelow_le_partialUnitriangularGroup hν)).1 hξ, ht⟩
  have hν_succ : ν ∈ unipotentBelow (a + 1) := by grind
  refine ⟨t, ht_mem, ν, hν_succ, Γ.hasMatrixSize_boxSet h_box, ?_⟩
  rintro n hn ⟨μ, hμ, hy⟩
  -- Put `δ = n n₀⁻¹`; the translating element is `t δ t⁻¹`.
  let δ : T.G := n * n₀⁻¹
  have hδ : δ ∈ floorUnipotent a := mul_mem hn (inv_mem hn₀)
  have h_move : t * n * (t * n₀)⁻¹ ∈ floorUnipotent a := by
    obtain ⟨s, hs, r, hr, rfl⟩ : ∃ s ∈ floorGroup (a + 1), ∃ r ∈ floorUnipotent a, t = s * r :=
      exists_floorGroup_mul_floorUnipotent ht_mem
    have h_inner : r * δ * r⁻¹ ∈ floorUnipotent a := mul_mem (mul_mem hr hδ) (inv_mem hr)
    have h_outer : s * (r * δ * r⁻¹) * s⁻¹ ∈ floorUnipotent a :=
      conj_mem_floorUnipotent h_inner s hs
    simpa [δ, mul_assoc] using h_outer
  -- The translate is `t δ ν ν₀ n₀ y`, and `κ = t ν μ δ (ν ν₀)⁻¹ δ⁻¹ t⁻¹` moves it to `t ν μ n y`.
  let κ : T.G := t * (ν * μ * (δ * (ν * ν₀)⁻¹ * δ⁻¹)) * t⁻¹
  have h_conj : δ * (ν * ν₀)⁻¹ * δ⁻¹ ∈ unipotentBelow a :=
    conj_mem_unipotentBelow hδ.1 (inv_mem (mul_mem hν hν₀))
  have hκ : κ ∈ unipotentBelow a := conj_mem_unipotentBelow ht (mul_mem (mul_mem hν hμ) h_conj)
  have h_close : t * n * (t * n₀)⁻¹ * (t * ν * (ν₀ * (n₀ * y))) ∈ Γ.closeBelow a (t * ν * g) :=
    ⟨κ, hκ, by simpa [κ, δ, mul_assoc] using hy⟩
  have h_start : (t * ν * g)⁻¹ * (t * ν * (ν₀ * (n₀ * y))) ∈ Γ.positionsOfSize := by
    simpa [mul_assoc] using hy₀
  simpa [mul_assoc] using Γ.exists_lift_of_mem_closeBelow a h_box h_start h_move h_close

-- Keeps definitional checks from unfolding the finite sums.
seal Finset.sum in
/-- One floor up. Let `Γ` be a gauge (size bounds for the place data `F`), `k` a pairing kernel for
`F` whose twist `d` commutes with G^(j) = `floorGroup j`, and `j ≤ l ≤ ϱ`. The cut square
`Γ.cutSquare k l g y` is the squared modulus of the correlation `k` above floor `l`. It is set to
zero where the positions of `(g, y)` in the position ball have measure zero. Its integral over `n`
against `heisenbergMeasure l`, taken at `(g, n * y)`, is at most the step cost `Γ.climbConst l`
times the integral of `Γ.cutSquare k (l + 1)` at `(σ * g, σ * y)` against `F.floorMeasure (l + 1)`.
Below the top floor this is Parseval's formula; on the top floor it is Cauchy–Schwarz on
H = `T.besselH`. -/
lemma Gauge.lintegral_cutSquare_le (Γ : Gauge F) {k : T.G → T.G → ℂ} {d : T.G} {l : ℕ}
    (hK : F.IsPairingKernel j k d) (hjl : j ≤ l) (hl : l ≤ 𝔰.ϱ) (g y : T.G) :
    ∫⁻ n : T.G, Γ.cutSquare k l g (n * y) ∂heisenbergMeasure l ≤
      Γ.climbConst l *
        ∫⁻ σ : T.G, Γ.cutSquare k (l + 1) (σ * g) (σ * y) ∂F.floorMeasure (l + 1) := by
  have h_positions : MeasurableSet Γ.positionsOfSize := Γ.measurableSet_positionsOfSize
  by_cases h_closeMass : Γ.closeMass (l + 1) g y = 0
  · -- Then `Γ.closeMass l g (n * y) = 0` for almost every `n`, since the measure of the
    -- unipotent group of the first `l + 1` floors is that of the first `l` floors convolved with
    -- `heisenbergMeasure l`.
    have h_meas : Measurable fun n : T.G ↦ Γ.closeMass l g (n * y) := by
      unfold closeMass
      fun_prop
    have h_zero : ∫⁻ n : T.G, Γ.closeMass l g (n * y) ∂heisenbergMeasure l = 0 := by
      simpa (disch := fun_prop) [closeMass, ascConv, lintegral_mconv_symm, mul_assoc]
        using h_closeMass
    calc ∫⁻ n : T.G, Γ.cutSquare k l g (n * y) ∂heisenbergMeasure l
        ≤ ∫⁻ n : T.G, ∞ * Γ.closeMass l g (n * y) ∂heisenbergMeasure l :=
          lintegral_mono fun n ↦ inf_le_left
      _ = 0 := by rw [lintegral_const_mul _ h_meas, h_zero, mul_zero]
      _ ≤ _ := zero_le
  -- Otherwise the truncation on the right does nothing: by `closeMass_mul_mul` the mass of the
  -- position ball is the same at `σ g`, `σ y`.
  suffices h_uncut :
      ∫⁻ n : T.G, (∞ * Γ.closeMass l g (n * y)) ⊓ ‖F.partialCorrelation (l + 1) k g (n * y)‖ₑ ^ 2
          ∂heisenbergMeasure l ≤
        Γ.climbConst l * ∫⁻ σ : T.G, ‖F.partialCorrelation (l + 1 + 1) k (σ * g) (σ * y)‖ₑ ^ 2
          ∂F.floorMeasure (l + 1) by
    simpa +contextual only [cutSquare, Γ.closeMass_mul_mul
      (ascConv_heisenbergMeasure_dirac_comm _ _),
      top_mul h_closeMass, top_inf_eq] using h_uncut
  unfold climbConst
  split_ifs with hlϱ
  · -- Below the top floor this is Parseval, `Gauge.parseval_heisenbergMeasure_le`, at the
    -- frequency `F.levelUnit⁻¹`; on `floorUnipotent l` the function `Γ.cutSquare k l g (· * y)`
    -- vanishes off the set `S`.
    let a : Fin 𝔰.ϱ := ⟨l, hlϱ⟩
    let S : Set T.G :=
      {n ∈ floorUnipotent l | n * y ∈ Γ.closeBelow l g ∧ F.IsNear (l + 1) g}
    have h_twist (s : T.G) (hs : s ∈ floorUnipotent l) :
        F.levelUnit⁻¹.val * (simpleRootSum (d * s * d⁻¹) - simpleRootSum (s ^ 0)) =
          F.levelUnit⁻¹.val * simpleRootSum s := by
      simp [hK.conj_eq_self _ (floorGroup_anti hjl hs.1), simpleRootSum_eq_zero_of_mem_besselH]
    have h_supp (n : T.G) (hn : n ∈ floorUnipotent l) (h_ne : Γ.cutSquare k l g (n * y) ≠ 0) :
        n ∈ S := by
      obtain ⟨h_mass, h_up⟩ : Γ.closeMass l g (n * y) ≠ 0 ∧
          F.partialCorrelation (l + 1) k g (n * y) ≠ 0 := by
        simpa [cutSquare] using h_ne
      obtain ⟨ν, hν, h_pos⟩ : ∃ ν ∈ unipotentBelow l,
          Γ.positionsOfSize.indicator (1 : T.G → ℝ≥0∞) (g⁻¹ * (ν * (n * y))) ≠ 0 :=
        exists_ne_zero_of_ae ae_ascConv_mem_unipotentBelow h_mass
      exact ⟨hn, ⟨ν, hν, Set.mem_of_indicator_ne_zero h_pos⟩,
        hK.isNear_of_partialCorrelation_ne_zero h_up⟩
    have h_centre : ∀ n₀ ∈ S, ∃ t ∈ partialUnitriangularGroup (a + 1) ⊓ floorGroup a,
        ∃ ν ∈ unipotentBelow (a + 1), Γ.HasMatrixSize 1 (t * ν * g).val.val ∧
          ∀ n ∈ S, ∃ v : 𝔰.BesselIndex → A,
            CongrBelow a (((t * n₀ * (t * n)⁻¹).val.val - 1) *ᵥ Pi.single (eStar a) 1) v ∧
            F.levelUnit⁻¹.val • v ∈ Γ.vecsOfSize 17 := by
      rintro n₀ ⟨hn₀, ⟨ν₀, hν₀, hy₀⟩, h_near⟩
      obtain ⟨t, ht, ν, hν, h_size, h_lift⟩ := Γ.exists_centre_of_isNear a h_near hn₀ hν₀ hy₀
      exact ⟨t, ht, ν, hν, h_size, fun n ⟨hn, h_close, _⟩ ↦ h_lift n hn h_close⟩
    refine (Γ.parseval_heisenbergMeasure_le a (ξ := F.levelUnit⁻¹) (u := F.levelUnit) (ε := 0)
      (C := 1)
      (hK.mono (hjl.trans l.le_succ)) g y h_twist
      (fun n hn h_ne ↦ ⟨h_supp n hn h_ne, by simp [a, cutSquare]⟩) h_centre).trans ?_
    -- The constant of Parseval's inequality is `Γ.floorConst l`.
    have h_freq : P.modulus (F.levelUnit⁻¹.val * F.levelUnit.val) = 1 := by simp
    have h_exp : 100 * 𝔰.n * (1 + 17 + 31) = 4900 * 𝔰.n := by ring
    rw [h_freq, h_exp, div_one, one_mul, floorConst]
    exact le_of_eq (by ring)
  · -- On the top floor `heisenbergMeasure l` is the unit mass, and Cauchy–Schwarz costs the
    -- constant 1.
    have hl_top : l = 𝔰.ϱ := by lia
    obtain ⟨-, -, h_mass⟩ := F.measureH_mem_and_invariant_and_le_one
    have h_vol : F.FloorMassLe (l + 1) 1 1 := fun g' ↦ by
      have h_le : F.measureH {h : T.G | ∃ u ∈ besselU, u * (h * g') ∈ F.boxSet} ≤ 1 := h_mass g'
      -- Without `Subtype.exists` both sets keep the same form.
      simpa [IsNear, hl_top, -Subtype.exists] using h_le
    grw [heisenbergMeasure_eq_dirac_one (by lia),
      ← hK.pivotL1Norm_sq_le_of_floorMassLe_one h_vol, ← hK.enorm_partialCorrelation_le]
    simp

/-- All floors above `l`. Let `k` be a pairing kernel at floor `j` and `j ≤ l ≤ ϱ + 1`. The Haar
measure `F.groupMeasure` factors as the convolution of `ascConv heisenbergMeasure l`, the measure of
the unipotent group of the first `l` floors, with an s-finite measure `ρ`; and the integral of the
cut square against `ρ` and the floors up to `l`, times the costs of the floors below `l`, is at most
the product of all costs times the squared L² norm of the kernel.

The factorization is a form of Weil's quotient integral formula for the unipotent group of the
first `l` floors, with an s-finite measure `ρ` on the group in place of the invariant measure on
cosets. -/
lemma Gauge.exists_factor_cutSquare_le (Γ : Gauge F) [F.groupMeasure.IsHaarMeasure]
    {k : T.G → T.G → ℂ} {d : T.G} {l : ℕ} (hK : F.IsPairingKernel j k d) (hjl : j ≤ l)
    (hl : l ≤ 𝔰.ϱ + 1) :
    ∃ ρ : Measure T.G, SFinite ρ ∧
      F.groupMeasure = ascConv heisenbergMeasure l ∗ₘ ρ ∧
      (∏ a ∈ range l, Γ.climbConst a) *
          ∫⁻ g : T.G, ∫⁻ y : T.G, Γ.cutSquare k l g y ∂ρ ∂descConv F.floorMeasure 0 (l + 1) ≤
        (∏ a ∈ range 𝔰.ϱ, Γ.floorConst a) *
          ∫⁻ g : T.G, ∫⁻ y : T.G, ‖k g y‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 ∂F.quotientMeasureFrom
            0 := by
  have h_meas (l : ℕ) : Measurable ↿(Γ.cutSquare k l) := Γ.measurable_cutSquare hK l
  induction hl using Nat.decreasingInduction with
  | self =>
    refine ⟨F.quotientMeasureFrom 0, inferInstance, by
      simp [partialGroupMeasure_zero_eq, ascConv], ?_⟩
    -- Above the top floor the kernel is not averaged and there is no cost.
    gcongr ?_ * ∫⁻ g, ∫⁻ y, ?_ ∂_ ∂_
    · simp [climbConst, prod_range, Fin.prod_univ_castSucc]
    · simp [cutSquare, partialCorrelation, descConv]
  | of_succ l hl ih =>
    -- By induction there is such a measure `ρ` for `l + 1`.
    obtain ⟨ρ, hρ, h_factor_succ, h_mass⟩ := ih (by lia)
    have h_factor : F.groupMeasure = ascConv heisenbergMeasure l ∗ₘ (heisenbergMeasure l ∗ₘ ρ) := by
      rw [h_factor_succ, ascConv, mconv_assoc]
    refine ⟨heisenbergMeasure l ∗ₘ ρ, inferInstance, h_factor, le_trans ?_ h_mass⟩
    grw [prod_range_succ, mul_assoc, descConv_succ (l + 1), lintegral_mconv_symm (by fun_prop),
      ← lintegral_const_mul (Γ.climbConst l) (by fun_prop)]
    gcongr with g
    -- `Γ.cutSquare k (l + 1) g'` is left invariant under `unipotentBelow (l + 1)`, so
    -- `lintegral_mul_left_eq_of_factor` lets `y` move by `σ`.
    have h_shift (σ : T.G) (hσ : σ ∈ floorGroup (l + 1)) :
        ∫⁻ y, Γ.cutSquare k (l + 1) (σ * g) (σ * y) ∂ρ =
          ∫⁻ y, Γ.cutSquare k (l + 1) (σ * g) y ∂ρ := by
      refine lintegral_mul_left_eq_of_factor h_factor_succ ae_ascConv_mem_unipotentBelow
        (fun ν hν ↦ (ascConv_heisenbergMeasure_invariant hν).1)
        (ascConv_heisenbergMeasure_dirac_comm _ hσ) (by fun_prop) fun ν hν y ↦ ?_
      have h_closeMass :
          Γ.closeMass (l + 1) (σ * g) (ν * y) = Γ.closeMass (l + 1) (σ * g) y := by
        simpa using Γ.closeMass_mul_mul (σ := 1) (g := σ * g) (y := y)
          (by simp [ascConv_heisenbergMeasure_invariant hν])
      simp [cutSquare, h_closeMass, hK.enorm_partialCorrelation_mul_of_mem_unipotentBelow hν]
    -- Apply `lintegral_cutSquare_le` for each `y`, swap the integrals and undo the shift.
    calc ∫⁻ y, Γ.cutSquare k l g y ∂heisenbergMeasure l ∗ₘ ρ
        = ∫⁻ y, ∫⁻ n, Γ.cutSquare k l g (n * y) ∂heisenbergMeasure l ∂ρ :=
          lintegral_mconv_symm (by fun_prop)
      _ ≤ ∫⁻ y, Γ.climbConst l *
            ∫⁻ σ, Γ.cutSquare k (l + 1) (σ * g) (σ * y) ∂F.floorMeasure (l + 1) ∂ρ :=
          lintegral_mono fun y ↦ Γ.lintegral_cutSquare_le hK hjl hl.le_pred g y
      _ = Γ.climbConst l *
            ∫⁻ σ, ∫⁻ y, Γ.cutSquare k (l + 1) (σ * g) (σ * y) ∂ρ ∂F.floorMeasure (l + 1) := by
          rw [lintegral_const_mul _ (by fun_prop), lintegral_lintegral_swap (by fun_prop)]
      _ = Γ.climbConst l *
            ∫⁻ σ, ∫⁻ y, Γ.cutSquare k (l + 1) (σ * g) y ∂ρ ∂F.floorMeasure (l + 1) := by
          rw [lintegral_floorMeasure_congr rfl h_shift]

/-- One frame, one pivot. Let `k` be a pairing kernel at floor `j` and `j ≤ l ≤ ϱ`. Over the
position ball `Γ.positionsOfSize`, the squared modulus of the correlation above floor `l`, weighted
by `F.depthWeight l`, has integral at most the product of the costs `Γ.floorConst` of the floors
times the squared L² norm of the kernel. -/
theorem Gauge.lintegral_weightedSquare_le (Γ : Gauge F) [F.groupMeasure.IsHaarMeasure]
    {k : T.G → T.G → ℂ} {d : T.G} {l : ℕ} (hK : F.IsPairingKernel j k d) (hjl : j ≤ l)
    (hl : l ≤ 𝔰.ϱ) :
    ∫⁻ x : T.G in Γ.positionsOfSize, ∫⁻ g : T.G, F.weightedSquare l k x g
        ∂descConv F.floorMeasure 0 (l + 1) ∂F.groupMeasure ≤
      (∏ a ∈ range 𝔰.ϱ, Γ.floorConst a) *
        ∫⁻ g : T.G, ∫⁻ y : T.G, ‖k g y‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 ∂F.quotientMeasureFrom 0 := by
  -- Put `x = g⁻¹ ν y` with `ν` in the unipotent group of the first `l` floors. The modulus of the
  -- correlation does not depend on `ν`, and the weight has bounded integral over `ν`.
  have h_positions : MeasurableSet Γ.positionsOfSize := Γ.measurableSet_positionsOfSize
  have h_meas : Measurable ↿(Γ.cutSquare k l) := Γ.measurable_cutSquare hK l
  obtain ⟨ρ, hρ, h_factor, h_mass⟩ := Γ.exists_factor_cutSquare_le hK hjl hl.step
  grw [← h_mass, lintegral_lintegral_swap (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
  gcongr with g
  suffices h_inner : ∀ y : T.G,
      ∫⁻ ν, Γ.positionsOfSize.indicator (F.weightedSquare l k · g) (g⁻¹ * (ν * y))
          ∂ascConv heisenbergMeasure l ≤
        (∏ a ∈ range l, Γ.climbConst a) * Γ.cutSquare k l g y by
    rw [← lintegral_indicator h_positions, ← lintegral_mul_left_eq_self _ g⁻¹, h_factor,
      lintegral_mconv_symm (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
    exact lintegral_mono h_inner
  intro y
  have h_bound : (∫⁻ ν, Γ.positionsOfSize.indicator (F.depthWeight l g) (g⁻¹ * (ν * y))
        ∂ascConv heisenbergMeasure l) * ‖F.partialCorrelation (l + 1) k g y‖ₑ ^ 2 ≤
      (∏ a ∈ range l, Γ.climbConst a) * Γ.cutSquare k l g y := by
    by_cases h_up : F.partialCorrelation (l + 1) k g y = 0
    · simp [h_up]
    by_cases h_closeMass : Γ.closeMass l g y = 0
    · -- Almost no `ν` has `g⁻¹ ν y` in `Γ.positionsOfSize`, so the integral of the weight vanishes.
      rw [lintegral_congr_of_ae_imp ((lintegral_eq_zero_iff (by fun_prop)).1 h_closeMass)
        (g := fun _ ↦ 0) (by simp +contextual)]
      simp
    · have h_near : F.IsNear l g := (hK.isNear_of_partialCorrelation_ne_zero h_up).anti l.le_succ
      rw [cutSquare, top_mul h_closeMass, top_inf_eq]
      grw [Γ.lintegral_depthWeight_le hl g y h_near]
      gcongr with a ha
      have ha_lt : a < 𝔰.ϱ := (mem_range.1 ha).trans_le hl
      rw [climbConst, ite_eq_left ha_lt]
  refine le_of_eq_of_le ?_ h_bound
  rw [← lintegral_mul_const _ (by fun_prop)]
  refine lintegral_congr_of_ae_imp ae_ascConv_mem_unipotentBelow fun ν hν ↦ ?_
  simp [weightedSquare, hK.enorm_partialCorrelation_mul_of_mem_unipotentBelow hν, Set.indicator]

/-- **One frame.** Let `k` be a pairing kernel at floor `j ≤ ϱ`. Over the position ball
`Γ.positionsOfSize`, the integral of `F.weightedSquareIntegral j k` for `F.groupMeasure` is at most
`𝔰.n` = ϱ + 1 times the product of the costs `Γ.floorConst l`, l < ϱ, times the squared L² norm of
`k` for `F.quotientMeasureFrom 0` in each variable. -/
theorem Gauge.lintegral_weightedSquareIntegral_le (Γ : Gauge F) [F.groupMeasure.IsHaarMeasure]
    {k : T.G → T.G → ℂ} {d : T.G} (hK : F.IsPairingKernel j k d) (hj : j ≤ 𝔰.ϱ) :
    ∫⁻ x : T.G in Γ.positionsOfSize, F.weightedSquareIntegral j k x ∂F.groupMeasure ≤
      𝔰.n * ((∏ l ∈ range 𝔰.ϱ, Γ.floorConst l) *
        ∫⁻ g : T.G, ∫⁻ y : T.G, ‖k g y‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 ∂F.quotientMeasureFrom 0) :=
  lintegral_weightedSquareIntegral_le_of_lintegral_le hK hj fun hjl hl ↦
    Γ.lintegral_weightedSquare_le hK hjl hl

/-- Let `p`, `q` be sequences of units of the ring `A` of the place `P`, with modulus |·|, let
`j ≤ ϱ` and r_a = `𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1))`. In the product over a < j of |p_a q_a|^(r_a) (the
squared `F.headDensity`), |p_a|^(-(2 r_a + 1)) (the squared `F.floorModulus`) and
|p_a / q_a|^(r_a + 1), the powers of |p_a| cancel and |q_0 ⋯ q_(j-1)|⁻¹ is left. -/
lemma PlaceData.headDensity_sq_mul_eq_modulus (F : PlaceData ι T m) (p q : ℕ → Aˣ) (hj : j ≤ 𝔰.ϱ) :
    F.headDensity j p q ^ 2 * (∏ a ∈ range j, F.floorModulus a (p a)⁻¹) ^ 2 *
        ∏ a ∈ range j, P.modulus (p a / q a).val ^ (𝔰.k + 2 * (𝔰.ϱ - a)) =
      P.modulus (∏ a ∈ range j, q a)⁻¹.val := by
  rw [← Finset.prod_inv_distrib, Units.coe_prod, map_prod, headDensity, ← prod_pow, ← prod_pow,
    ← prod_mul_distrib, ← prod_mul_distrib]
  refine prod_congr rfl fun a ha ↦ ?_
  rw [floorModulus]
  set r : ℕ := 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)) with hr
  have h_exp : 𝔰.k + 2 * (𝔰.ϱ - a) = r + 1 := by grind
  have h_sqrt (z : ℝ≥0∞) : (z ^ (2⁻¹ : ℝ)) ^ 2 = z := rpow_inv_natCast_pow two_ne_zero z
  -- An identity of monomials in the units `p a`, `q a`: compare exponents additively.
  have h_units : (p a * q a) ^ r * (((p a)⁻¹ ^ r) ^ 2 * (p a)⁻¹) * (p a / q a) ^ (r + 1) =
      (q a)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_div]
    module
  rw [h_exp, pow_right_comm, h_sqrt, mul_pow, h_sqrt, ← h_units]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]

/-- Let `W` be a cut Bessel function, j ≤ ϱ, 𝖬 = `F.groupMeasure` a Haar measure, `p` any sequence
of units, `q` a head of length `j` for the gauge `Γ`, and `S` a subset of the position ball of the
gauge `Γ'`. Let `f` have the gain `e` on `S`: f(x)² is at most e² times
`Γ.weightedSquareProduct j p q W x`, the product of the two second moments at x with its constants.
Then `F.headDensity j p q` times ∫_S f d𝖬 is at most e times the squared norm `F.pairingNormSq W` of
the correlation, times the product over l < ϱ of the `F.floorModulus l`,
`P.kernelBound ^ (card F.FreeIndex * 𝔰.ϱ)`, Λ^(1500000 n³ + 1) and Λ'^(25000 n²), where
Λ = `Γ.loss`, Λ' = `Γ'.loss` and n = ϱ + 1. -/
theorem Gauge.headDensity_mul_lintegral_le_mul_pairingNormSq {p q : ℕ → Aˣ} {I : Type} [Fintype I]
    {W : T.G → EuclideanSpace ℂ I} (Γ Γ' : Gauge F) (hW_cut : F.IsCut W) (hj : j ≤ 𝔰.ϱ)
    [F.groupMeasure.IsHaarMeasure] (hq : Γ.IsHead j q) {S : Set T.G} {e : ℝ≥0∞} {f : T.G → ℝ≥0∞}
    (hS : S ⊆ Γ'.positionsOfSize)
    (h_point : ∀ x ∈ S, f x ^ 2 ≤ e ^ 2 * Γ.weightedSquareProduct j p q W x) :
    F.headDensity j p q * ∫⁻ x : T.G in S, f x ∂F.groupMeasure ≤
      e * (∏ l ∈ range 𝔰.ϱ, F.floorModulus l) * P.kernelBound ^ (card F.FreeIndex * 𝔰.ϱ) *
        Γ.loss ^ (1500000 * 𝔰.n ^ 3) * Γ'.loss ^ (25000 * 𝔰.n ^ 2) * F.pairingNormSq W *
          Γ.loss := by
  -- Square both sides. Cauchy–Schwarz splits the integral into two integrals of
  -- `weightedSquareIntegral`, which `Gauge.lintegral_weightedSquareIntegral_le` bounds by
  -- `pairingNormSq W`, the second up to the modulus `J` of left translation by `weylRatio j p q`.
  let D : ℝ≥0∞ := (∏ a ∈ range j, F.floorModulus a (p a)⁻¹) ^ 2
  let J : ℝ≥0∞ := ∏ a ∈ range j, P.modulus (p a / q a).val ^ (𝔰.k + 2 * (𝔰.ϱ - a))
  let V : ℝ≥0∞ := ∏ l ∈ range 𝔰.ϱ, Γ'.floorConst l
  have h_mod : F.headDensity j p q ^ 2 * D * J ≤ Γ.loss ^ 2 :=
    (F.headDensity_sq_mul_eq_modulus p q hj).trans_le
      (Γ.modulus_le 2 _ (Γ.mem_ofSize_mono (hq j le_rfl)))
  have ker₁ : F.IsPairingKernel 0 (frameCorrelation W 1) 1 :=
    Γ.isPairingKernel_frameCorrelation_one hW_cut 0
  have ker₂ : F.IsPairingKernel j (frameCorrelation W (weylRatio j p q)) (weylRatio j p q) :=
    Γ.isPairingKernel_frameCorrelation hW_cut j p q
  have hW_meas : StronglyMeasurable W := hW_cut.stronglyMeasurable
  let N₁ : T.G → ℝ≥0∞ := F.weightedSquareIntegral 0 (frameCorrelation W 1)
  let N₂ : T.G → ℝ≥0∞ := F.weightedSquareIntegral j (frameCorrelation W (weylRatio j p q))
  let E₁ : ℝ≥0∞ := ∫⁻ x in Γ'.positionsOfSize, N₁ x ∂F.groupMeasure
  let E₂ : ℝ≥0∞ := ∫⁻ x in Γ'.positionsOfSize, N₂ x ∂F.groupMeasure
  have h_cs : (∫⁻ x in S, f x ∂F.groupMeasure) ^ 2 ≤
      e ^ 2 * (D * Γ.floorsConst ^ 3 * E₁) * E₂ := by
    -- Bound `f`, which need not be measurable, by a square root; then enlarge `S`.
    let u : T.G → ℝ≥0∞ := fun x ↦ (e ^ 2 * Γ.weightedSquareProduct j p q W x) ^ (2⁻¹ : ℝ)
    have hu_meas : Measurable u := by fun_prop [weightedSquareProduct, weightedSquareIntegral]
    have hN₁ : Measurable N₁ := by fun_prop [weightedSquareIntegral]
    have hN₂ : Measurable N₂ := by fun_prop [weightedSquareIntegral]
    have hf_le (x : T.G) (hx : x ∈ S) : f x ≤ u x :=
      (le_rpow_inv_iff two_pos).2 (mod_cast h_point x hx)
    have hu_sq (x : T.G) : u x ^ 2 ≤ e ^ 2 * (D * Γ.floorsConst ^ 3 * N₁ x) * N₂ x :=
      (rpow_inv_natCast_pow two_ne_zero _).trans_le
        (by rw [weightedSquareProduct, mul_assoc (e ^ 2)])
    calc (∫⁻ x in S, f x ∂F.groupMeasure) ^ 2
        ≤ (∫⁻ x in Γ'.positionsOfSize, u x ∂F.groupMeasure) ^ 2 := by
          grw [setLIntegral_mono hu_meas hf_le, lintegral_mono_set hS]
      _ ≤ (∫⁻ x in Γ'.positionsOfSize, e ^ 2 * (D * Γ.floorsConst ^ 3 * N₁ x) ∂F.groupMeasure) *
            E₂ :=
          sq_lintegral_le (by fun_prop) (by fun_prop) hu_sq
      _ = e ^ 2 * (D * Γ.floorsConst ^ 3 * E₁) * E₂ := by
          rw [lintegral_const_mul _ (by fun_prop), lintegral_const_mul _ hN₁]
  have hE₁ : E₁ ≤ 𝔰.n * (V * F.pairingNormSq W) := by
    simpa only [V, PlaceData.pairingNormSq, frameCorrelation, one_mul] using
      Γ'.lintegral_weightedSquareIntegral_le ker₁ zero_le
  have hE₂ : E₂ ≤ 𝔰.n * (V * (J * F.pairingNormSq W)) := by
    -- Left translation by `weylRatio j p q` multiplies the inner integral by `J`.
    have h_translate (g : T.G) :
        ∫⁻ y, ‖⟪W g, W (weylRatio j p q * y)⟫_ℂ‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 =
          J * ∫⁻ y, ‖⟪W g, W y⟫_ℂ‖ₑ ^ 2 ∂F.quotientMeasureFrom 0 :=
      lintegral_weylRatio_mul (Φ := fun y ↦ ‖⟪W g, W y⟫_ℂ‖ₑ ^ 2) hj (by fun_prop)
    rw [PlaceData.pairingNormSq, ← lintegral_const_mul J (by fun_prop),
      ← lintegral_congr h_translate]
    exact Γ'.lintegral_weightedSquareIntegral_le ker₂ hj
  have h_rank : (𝔰.n : ℝ≥0∞) ≤ Γ'.loss ^ 𝔰.n := by
    grw [← Γ'.two_le_loss]
    exact_mod_cast 𝔰.n.lt_two_pow_self.le
  let C : ℝ≥0∞ :=
    (∏ l ∈ range 𝔰.ϱ, F.floorModulus l) * P.kernelBound ^ (card F.FreeIndex * 𝔰.ϱ)
  have h_floors : Γ'.loss ^ 𝔰.n * V ≤ C * Γ'.loss ^ (25000 * 𝔰.n ^ 2) := by
    have h_exp : 𝔰.n + 4900 * 𝔰.n * 𝔰.ϱ ≤ 25000 * 𝔰.n ^ 2 := by nlinarith
    grw [← pow_le_pow_right₀ Γ'.one_le_loss h_exp]
    simp only [C, V, prod_mul_distrib, prod_const, card_range, ← pow_mul, pow_add]
    exact le_of_eq (by ring)
  -- It remains to collect the constants; `h_rank` and `h_floors` bound those that come from `Γ'`.
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, mul_pow]
  calc F.headDensity j p q ^ 2 * (∫⁻ x in S, f x ∂F.groupMeasure) ^ 2
      ≤ F.headDensity j p q ^ 2 *
          (e ^ 2 * (D * Γ.floorsConst ^ 3 * (𝔰.n * (V * F.pairingNormSq W))) *
            (𝔰.n * (V * (J * F.pairingNormSq W)))) := by grw [h_cs, hE₁, hE₂]
    _ = F.headDensity j p q ^ 2 * D * J * e ^ 2 * Γ.floorsConst ^ 3 * (𝔰.n * V) ^ 2 *
          F.pairingNormSq W ^ 2 := by ring
    _ ≤ Γ.loss ^ 2 * e ^ 2 * Γ.floorsConst ^ 3 * (C * Γ'.loss ^ (25000 * 𝔰.n ^ 2)) ^ 2 *
          F.pairingNormSq W ^ 2 := by grw [h_mod, h_rank, h_floors]
    _ = _ := by
      simp only [C, floorsConst]
      ring

end New.Floors

end
