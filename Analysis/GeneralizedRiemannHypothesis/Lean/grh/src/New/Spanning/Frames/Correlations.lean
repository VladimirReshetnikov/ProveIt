import New.Spanning.Frames.Levels
import New.Spanning.Frames.TwoGauges

/-!
# The scale, near points and partial correlations

The structure `New.Floors.Gauge` collects the few facts about a place that the estimates use. A
correlation is a kernel on pairs of points with a character law; integrating it over the floors from
`l` on gives the partial correlations. The letters G^(l), R^(l), U_(<l) are those of the head of
`New.Spanning.Frames.Lengths`, and K, M those of `New.Spanning.Frames.Levels`.

## Main definitions and results

* `New.Floors.Gauge`, `New.Floors.Gauge.positionsOfSize`: a scale with its constant Λ =
  `Γ.loss`, and the close positions.
* `New.Floors.PlaceData.IsPairingKernel`, `New.Floors.PlaceData.partialCorrelation`: kernels and
  partial correlations.
* `New.Floors.PlaceData.weightedSquare`, `New.Floors.PlaceData.weightedSquareIntegral`: the second
  moments of one frame.
* `New.Floors.Gauge.isBalanced_of_isNear`: near points are balanced.

Notions from other files:
* `New.Floors.PlaceData`: the data of a place, among them the level M = `F.levelUnit`, the compact
  set K = `F.boxSet` of the unitary group G = `T.G`, and the set `F.positions` of the elements by
  which the second point of a pair differs from the first.
* `New.Floors.PlaceData.IsNear`: g is near at j if R^(j) g meets K, for R^(j) =
  `partialUnitriangularGroup j`.
* `New.Floors.PlaceData.floorMeasure`, `New.Floors.PlaceData.quotientMeasureFrom`: the measure of
  floor l on G^(l) = `floorGroup l`, and the convolution of the measures of the floors from l on.
* `New.Floors.Size`: a filtration `ofSize i` of the numbers by size; a vector or a matrix has size i
  if all its entries have.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

section LevelGauge

open Matrix MeasureTheory Measure BesselIndex ENNReal Fintype FloorGroups Place TraceOne Function
  Filter

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔰 : Shape} {T : 𝔰.Form A} {m : ℕ}
  [IsHermitianUnit T.splitGram] (F : PlaceData ι T m)

namespace PlaceData

variable (j : ℕ) (k : T.G → T.G → ℂ) (w x g y : T.G) (K : ℝ≥0∞)

/-- For every g, the integral of c(σ g) for the measure of floor j, over the σ with σ g near at
j + 1 (`IsNear`), is at most the bound `K` (a number, not the compact set `F.boxSet`). -/
def FloorMassLe (c : T.G → ℝ≥0∞) : Prop :=
  ∀ g : T.G,
    ∫⁻ σ : T.G in {σ : T.G | F.IsNear (j + 1) (σ * g)}, c (σ * g) ∂F.floorMeasure j ≤ K

/-- The correlation from floor j on: the integral of k(x g, x y) in x for `F.quotientMeasureFrom j`,
the measure on G that represents the quotient (U ∩ G^(j)) ∖ G^(j), where U = `besselU`. -/
def partialCorrelation : ℂ := ∫ x : T.G, k (x * g) (x * y) ∂F.quotientMeasureFrom j

/-- The rules for a kernel k on G × G and an element w that commutes with G^(j). They hold for the
correlation k(g, y) = ⟪W g, W (w y)⟫ of a Bessel function W. -/
structure IsPairingKernel : Prop where
  /-- The kernel is jointly measurable. -/
  measurable : Measurable ↿k
  /-- For n, n' in U_(<l) = `unipotentBelow l`, putting n before g and n' before y multiplies the
  correlation from floor l + 1 on by ψ((σ₀(w n' w⁻¹) - σ₀(n)) / M), where σ₀ = `simpleRootSum`, ψ is
  the additive character of the place and M = `F.levelUnit` is the level. -/
  equivariance : ∀ {l : ℕ} {n n' : T.G}, n ∈ unipotentBelow l → n' ∈ unipotentBelow l → ∀ g y : T.G,
    F.partialCorrelation (l + 1) k (n * g) (n' * y) =
      ψ (F.levelUnit⁻¹.val * (simpleRootSum (w * n' * w⁻¹) - simpleRootSum n)) *
        F.partialCorrelation (l + 1) k g y
  /-- The element w commutes with G^(j). -/
  conj_eq_self : ∀ s ∈ floorGroup j, w * s * w⁻¹ = s
  /-- The integral of |k(x g, x y)| over the floors from l on has a finite bound that does not
  depend on g and y. -/
  exists_lintegral_le (l : ℕ) :
    ∃ c < ∞, ∀ g y : T.G, ∫⁻ x : T.G, ‖k (x * g) (x * y)‖ₑ ∂F.quotientMeasureFrom l ≤ c
  /-- If the correlation of g and y from floor l on is not zero, then g is near at l. -/
  isNear_of_partialCorrelation_ne_zero : ∀ {l : ℕ} {g y : T.G},
    F.partialCorrelation l k g y ≠ 0 → F.IsNear l g

/-- The function of z that is the inverse of the weight `F.depthWeight j z x` of length j at the
points z and z x if z is near at j, and 0 elsewhere. -/
def invDepthWeight : T.G → ℝ≥0∞ :=
  {z : T.G | F.IsNear j z}.indicator fun z : T.G ↦ (F.depthWeight j z x)⁻¹

/-- The integral over the σ in floor j of the modulus of the correlation of σ g and σ y from floor
j + 1 on. -/
def pivotL1Norm : ℝ≥0∞ :=
  ∫⁻ σ : T.G, ‖F.partialCorrelation (j + 1) k (σ * g) (σ * y)‖ₑ ∂F.floorMeasure j

/-- The weight of length j times the squared modulus of the correlation from floor j + 1 on, both
taken at the points g and g x. -/
abbrev weightedSquare : ℝ≥0∞ := F.depthWeight j g x * ‖F.partialCorrelation (j + 1) k g (g * x)‖ₑ ^
  2

/-- The function b_j(g) = ∫ (a_j + b_{j+1})(σ g) dθ_j(σ) for j < n = `𝔰.n`, and 0 for j ≥ n, where
a_j is `New.Floors.PlaceData.weightedSquare` at the position x and θ_j = `F.floorMeasure j`. -/
def weightedSquareSum (x : T.G) (j : ℕ) (g : T.G) : ℝ≥0∞ :=
  if j < 𝔰.n then
    ∫⁻ σ : T.G,
      F.weightedSquare j k x (σ * g) + weightedSquareSum x (j + 1) (σ * g) ∂F.floorMeasure j
  else
    0

/-- The integral of `F.weightedSquareSum k x j`, the sum of the weighted squared correlations from
floor j on, over the floors below j. -/
def weightedSquareIntegral : ℝ≥0∞ := ∫⁻ g : T.G,
  F.weightedSquareSum k x j g ∂descConv F.floorMeasure 0 j

end PlaceData

/-- The data through which a gauge is used at either kind of place, for the data F: sizes of numbers
for one scale element, together with a number Λ = `loss` whose powers bound moduli and volumes, also
those of the products with close pairs. It is not the length itself: lengths at a point are bounded
by `New.Floors.Size.LengthLeAt`, and at a real place the length is `lengthAt`. The last two fields
are the facts that are proved separately at a real place and at the finite places. -/
structure Gauge extends Size T where
  /-- The constant Λ of the scale: losses are its powers. -/
  loss : ℝ≥0∞
  /-- The set of numbers of size j is compact. -/
  isCompact_ofSize (j : ℕ) : IsCompact (ofSize j)
  /-- Λ is at least 2. -/
  two_le_loss : 2 ≤ loss
  /-- Λ is finite. -/
  loss_ne_top : loss ≠ ∞
  /-- The number m of further hyperbolic pairs is at most 9 n. -/
  pairs_le : m ≤ 9 * 𝔰.n
  /-- The constant `P.kernelBound` in Plancherel's formula is at least 1. -/
  one_le_kernelBound : 1 ≤ P.kernelBound
  /-- The level M has size 1. -/
  levelUnit_mem_ofSize : (F.levelUnit : A) ∈ ofSize 1
  /-- The basis has size 1. -/
  hasMatrixSize_basisMatrix : toSize.HasMatrixSize 1 F.basisMatrix
  /-- The element of trace one, divided by the skew unit, has size 1. -/
  traceOne_div_mem_ofSize : element * skewUnit⁻¹.val ∈ ofSize 1
  /-- The elements of K = `F.boxSet` have size 1. -/
  hasMatrixSize_boxSet ⦃x : T.G⦄ : x ∈ F.boxSet → toSize.HasMatrixSize 1 x.val.val
  /-- For a close pair (ω₁, ω₂), the vectors ω₁ and (ω₁ - ω₂) / M have size 1. -/
  mem_vecsOfSize_of_mem_closePairs ⦃ω₁ ω₂ : 𝔰.BesselIndex → A⦄ : (ω₁, ω₂) ∈ F.closePairs →
    ω₁ ∈ toSize.vecsOfSize 1 ∧ F.levelUnit⁻¹.val • (ω₁ - ω₂) ∈ toSize.vecsOfSize 1
  /-- If 1 / M has size 1, some unit c with inverse of size i + 2 turns any two vectors of size i
  into a close pair. -/
  exists_unit_smul_mem_closePairs (i : ℕ) : F.levelUnit⁻¹.val ∈ ofSize 1 →
    ∃ c : Aˣ, c⁻¹.val ∈ ofSize (i + 2) ∧
      ∀ ω₁ ∈ toSize.vecsOfSize i, ∀ ω₂ ∈ toSize.vecsOfSize i,
        (c.val • ω₁, c.val • ω₂) ∈ F.closePairs
  /-- An invertible number of size j has modulus at most Λ^j. -/
  modulus_le (j : ℕ) (u : Aˣ) : (u : A) ∈ ofSize j → P.modulus u ≤ loss ^ j
  /-- The numbers of size j have volume at most Λ^(j+1). -/
  volume_ofSize_le (j : ℕ) : volume (ofSize j) ≤ loss ^ (j + 1)
  /-- There is room for two blocks among the orthonormal basis vectors. -/
  two_mul_blockRank_le : 2 * F.blockRank ≤ card ι
  /-- The quadrics of a block, of rank p = `F.blockRank`. The volume of A^p disintegrates along the
  standard form into an s-finite kernel, each measure of which gives mass at most Λ^(p (j+1)) to
  the vectors of size j. -/
  exists_blockKernel : ∃ l : ProbabilityTheory.Kernel (skewAdjoint A) (Fin F.blockRank → A),
      ProbabilityTheory.IsSFiniteKernel l ∧ IsDisintegration volume 1 l ∧
      ∀ (β : skewAdjoint A) (j : ℕ), l β (toSize.vecsOfSize j) ≤ loss ^ (F.blockRank * (j + 1))
  /-- Common vectors. For g in K, a position z and ϱ linear forms on X' = `F.FreeIndex → A` (the
  rows of v), let W = `F.commonVectors g z v` be the set of vectors killed by the forms and short
  (`IsShortFrom`) from g and g z. Some φ controls the products ⟨u, ω⟩ with ω ∈ W, in the sense of
  `IsCommonBound`. -/
  exists_commonBound : ∀ g ∈ F.boxSet, ∀ z ∈ F.positions, ∀ v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A,
      ∃ φ : (F.FreeIndex → A) → ℝ≥0∞, F.IsCommonBound toSize loss (F.commonVectors g z v) φ

/-- The constant Λ of a gauge is at least 1. -/
@[simp]
lemma Gauge.one_le_loss (Γ : Gauge F) : 1 ≤ Γ.loss := one_le_two.trans Γ.two_le_loss

/-- Let `y` and `γ⁻¹ y` be near at `l`: elements of `partialUnitriangularGroup l` move them into the
compact set `F.boxSet` of the place datum `F`. Then the leading minors of order `j ≤ l` of the
matrix `T.frameGram γ` of the products `h(e_a, γ e_b)` of the frame vectors, for the form `h` with
Gram matrix `T.splitGram`, lie in step `9 * 𝔰.n` of the filtration by size of every gauge `Γ`. -/
theorem Gauge.leadingMinor_mem_ofSize_of_isNear {F : PlaceData ι T m} (Γ : Gauge F) {l : ℕ}
    {γ y : T.G} (hy : F.IsNear l y) (hγy : F.IsNear l (γ⁻¹ * y))
    {j : Fin (𝔰.n + 1)} (hj : j.val ≤ l) :
    leadingMinor (T.frameGram γ.val.val) j ∈ Γ.ofSize (9 * 𝔰.n) := by
  obtain ⟨ξ, hξ, hξ_box⟩ : ∃ ξ ∈ partialUnitriangularGroup l, ξ * y ∈ F.boxSet := hy
  obtain ⟨ξ', hξ', hξ'_box⟩ : ∃ ξ' ∈ partialUnitriangularGroup l, ξ' * (γ⁻¹ * y) ∈ F.boxSet := hγy
  exact Size.leadingMinor_mem_ofSize hξ hξ' (Γ.hasMatrixSize_boxSet hξ_box)
    (Γ.hasMatrixSize_boxSet hξ'_box) hj

/-- The close positions of a gauge Γ for the place datum F: the positions z ∈ `F.positions` for
which the matrix (z - 1) / M has size 1, where M = `F.levelUnit` is the level. -/
def Gauge.positionsOfSize (Γ : Gauge F) : Set T.G :=
  {z ∈ F.positions | Γ.HasMatrixSize 1 (F.levelUnit⁻¹.val • (z.val.val - 1))}

end LevelGauge

end New.Floors

end

section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Set Function FloorGroups Size Place TraceOne PlaceData
  HyperbolicBasis Finset

variable {A ι : Type} {𝔰 : Shape} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [Place A] [Fintype ι] [DecidableEq ι] {m i j : ℕ} {a : Fin 𝔰.ϱ} {T : 𝔰.Form A}
  [IsHermitianUnit T.splitGram] {F : PlaceData ι T m} {Γ : Gauge F} {b : Fin 𝔰.n} {g x σ ξ : T.G}

namespace PlaceData

/-- Being near at j (some element of R^(j) = `partialUnitriangularGroup j` moves the point into
`F.boxSet`) does not change under left multiplication by an element ξ of R^(j). -/
@[simp]
lemma isNear_mul_iff (hξ : ξ ∈ partialUnitriangularGroup j) :
    F.IsNear j (ξ * g) ↔ F.IsNear j g := by
  constructor
  · rintro ⟨η, hη, h_box⟩
    refine ⟨η * ξ, mul_mem hη hξ, ?_⟩
    rwa [mul_assoc]
  · rintro ⟨η, hη, h_box⟩
    refine ⟨η * ξ⁻¹, mul_mem hη (inv_mem hξ), ?_⟩
    rwa [mul_assoc, inv_mul_cancel_left]

/-- If g is near at i (an element of `partialUnitriangularGroup i` moves it into `F.boxSet`), it is
near at every j ≤ i, since these groups decrease with i. -/
lemma IsNear.anti (h_near : F.IsNear i g) (hji : j ≤ i) : F.IsNear j g := by
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup i, ξ * g ∈ F.boxSet := h_near
  exact ⟨ξ, partialUnitriangularGroup_anti hji hξ, h_box⟩

/-- If x lies in G^(j) = `floorGroup j` and x g is near at some i ≥ j (an element of
`partialUnitriangularGroup i` moves it into `F.boxSet`), then g is near at j. -/
lemma IsNear.of_floorGroup_mul (h_near : F.IsNear i (x * g)) (hx : x ∈ floorGroup j)
    (hji : j ≤ i := by first | rfl | lia) :
    F.IsNear j g :=
  (isNear_mul_iff (mem_partialUnitriangularGroup_of_mem_floorGroup hx)).mp (h_near.anti hji)

open Pointwise in
/-- The set of points of the unitary group that are near at `j` for the place datum `F` (some
element of `partialUnitriangularGroup j` moves them into the compact set `F.boxSet`) is
measurable. -/
lemma measurableSet_isNear : MeasurableSet {g : T.G | F.IsNear j g} := by
  -- It is the product of the closed subgroup `partialUnitriangularGroup j` with the compact box, so
  -- closed.
  have h_closed : IsClosed (T.partialUnitriangularGroup j : Set T.G) :=
    isClosed_of_entries_eq_one (H := partialUnitriangularGroup j) .rfl
  have h_box : IsCompact F.boxSet := F.isCompact_boxSet_and_measurableSet_positions.1
  have h_eq : (T.partialUnitriangularGroup j : Set T.G) * F.boxSet = {g : T.G | F.IsNear j g} := by
    ext g
    constructor
    · rintro ⟨ξ, hξ, x, hx, rfl⟩
      refine ⟨ξ⁻¹, inv_mem hξ, ?_⟩
      rwa [inv_mul_cancel_left]
    · rintro ⟨ξ, hξ, hξ_box⟩
      exact ⟨ξ⁻¹, inv_mem hξ, ξ * g, hξ_box, inv_mul_cancel_left ξ g⟩
  rw [← h_eq]
  exact (h_closed.mul_right_of_isCompact h_box).measurableSet

/-- Suppose that on each floor a < n the σ with σ g near at a + 1 (`IsNear`) have mass at most V for
`F.floorMeasure a`, whatever g is. Then for every c the g with g c near at ϱ + 2 have mass at most
V^(n-l) for the measure `F.quotientMeasureFrom l` of the floors from l on. Here n = `𝔰.n` = ϱ + 1,
and ϱ is the number of hyperbolic pairs of the shape `𝔰`. -/
lemma quotientMeasureFrom_isNear_le {V : ℝ≥0∞} (hV : ∀ a : Fin 𝔰.n, F.FloorMassLe a V 1) (l : ℕ)
    (c : T.G) :
    F.quotientMeasureFrom l {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * c)} ≤ V ^ (𝔰.n - l) := by
  -- Induction on the number of floors: peel off the lowest floor `l`, which has mass `≤ V`.
  induction hi : 𝔰.n - l generalizing l c with
  | zero =>
    -- only `F.measureH` is left, where the mass is at most 1, or `F.quotientMeasureFrom l` is a
    -- unit mass
    obtain rfl | hl : l = 𝔰.ϱ + 1 ∨ 𝔰.ϱ + 2 - l = 0 := by lia
    · simp [descConv, IsNear, measureH_setOf_mul_mem_boxSet_le_one, -Subtype.exists]
    · simp [hl, descConv, indicator_apply_le']
  | succ i ih =>
    have hl : l < 𝔰.n := by lia
    have h_meas : MeasurableSet {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * c)} :=
      measurable_mul_const c measurableSet_isNear
    let mass (σ : T.G) : ℝ≥0∞ :=
      F.quotientMeasureFrom (l + 1) {x : T.G | F.IsNear (𝔰.ϱ + 2) (x * (σ * c))}
    let N : Set T.G := {σ : T.G | F.IsNear (l + 1) (σ * c)}
    have h_floor : F.floorMeasure l N ≤ V := by simpa using hV ⟨l, hl⟩ c
    -- if `σ * c` is not near at `l + 1`, no point `x * σ * c` with `x` on the higher floors is near
    have h_support : support mass ⊆ N := by
      have h_ae : ∀ᵐ x : T.G ∂F.quotientMeasureFrom (l + 1), x ∈ floorGroup (l + 1) :=
        ae_descConv_mem ae_floorMeasure_mem
      refine support_subset_iff'.2 fun σ hσ ↦ measure_eq_zero_iff_ae_notMem.2 ?_
      filter_upwards [h_ae] with x hx_floor hx
      exact hσ (IsNear.of_floorGroup_mul hx hx_floor)
    calc F.quotientMeasureFrom l {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * c)}
      _ = ∫⁻ σ : T.G, mass σ ∂F.floorMeasure l := by
        rw [quotientMeasureFrom_eq_succ_mconv, mconv_apply_eq_lintegral h_meas]
        simp only [mass, mem_ofPred_eq, mul_assoc]
      _ = ∫⁻ σ : T.G in N, mass σ ∂F.floorMeasure l :=
        (setLIntegral_eq_of_support_subset h_support).symm
      _ ≤ ∫⁻ _ : T.G in N, V ^ i ∂F.floorMeasure l :=
        lintegral_mono fun σ ↦ ih (l + 1) (σ * c) (by lia)
      _ ≤ V ^ (i + 1) := by grw [setLIntegral_const, h_floor, pow_succ]

end PlaceData

/-- Coordinates of a Heisenberg element. Let n = `heisenbergElem a t` have the parameters
t = (ω, β) on floor a, so that (n - 1) e*_a = ω + (β - τ ⟨ω, ω⟩) e_a, where τ = `element` has trace
one and ω is extended by zero. If v differs from (n - 1) e*_a only in the coordinates e_b, b < a
(`CongrBelow`), and v / u has size i, then ω / u and (β - τ ⟨ω, ω⟩) / u have size i. -/
lemma Size.mem_vecsOfSize_of_congrBelow_heisenbergElem {S : Size T} {u : Aˣ}
    {t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A} {v : 𝔰.BesselIndex → A}
    (h_congr : CongrBelow a
      (((heisenbergElem (T := T) a t).val.val - 1) *ᵥ Pi.single (eStar a) 1) v)
    (h_short : u⁻¹.val • v ∈ S.vecsOfSize i) :
    u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1 ∈ S.vecsOfSize i ∧
    u⁻¹ * (t.2.val - element * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ
      T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ t.1) ∈ S.ofSize i := by
  set ω : 𝔰.BesselIndex → A := inclMatrix A Subtype.val *ᵥ t.1 with hω
  have hω_low (k : 𝔰.BesselIndex) (hk : floorOf k ≤ a) : ω k = 0 := by
    simp [hω, inclMatrix_val_mulVec, hk.not_gt]
  have h_column : ((heisenbergElem (T := T) a t).val.val - 1) *ᵥ Pi.single (eStar a) 1 =
      ω + (t.2.val - element * star ω ⬝ᵥ T.splitGram *ᵥ ω) • Pi.single (inl a) 1 := by
    rw [sub_mulVec, one_mulVec, heisenbergElem_mulVec, ← hω]
    simp [splitGram_col, hω_low, add_assoc]
  rw [h_column] at h_congr
  have h_inl : v (inl a) = t.2.val - element * star ω ⬝ᵥ T.splitGram *ᵥ ω := by
    simp [h_congr (inl a) le_rfl, hω_low]
  refine ⟨fun k ↦ ?_, by simpa [h_inl] using h_short (inl a)⟩
  by_cases hk : floorOf k ≤ a
  · simp [hω_low k hk, S.zero_one_mem_ofSize]
  · have h_ne : k ≠ inl a := fun h ↦ hk (by simp [h])
    have h_level : a ≤ BesselIndex.level k := by grind [floorOf_level_cases k]
    have hv : v k = ω k := by simp [h_congr k h_level, h_ne]
    simpa [hv] using h_short k

omit [StarRing A] [TopologicalSpace A] [MeasureSpace A] [Place A] in
/-- The vector e*_a is orthogonal to the e_b with b < a. -/
lemma isOrthogonalBelow_single_eStar (a : Fin 𝔰.ϱ) :
    IsOrthogonalBelow a (Pi.single (eStar a) (1 : A) : 𝔰.BesselIndex → A) :=
  fun b hb ↦ Pi.single_eq_of_ne (by grind) 1

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- For n in G^(a) = `floorGroup a` and ν in U_(<a) = `unipotentBelow a`, the vector (ν n - 1) e*_a
differs from (n - 1) e*_a only in the coordinates e_b, b < a. -/
lemma congrBelow_sub_one_mulVec {n ν : T.G} (hn : n ∈ floorGroup a) (hν : ν ∈ unipotentBelow a) :
    CongrBelow a ((n.val.val - 1) *ᵥ Pi.single (eStar a) 1)
      (((ν * n).val.val - 1) *ᵥ Pi.single (eStar a) 1) := by
  have h_orth : IsOrthogonalBelow a (n.val.val *ᵥ Pi.single (eStar a) (1 : A)) :=
    (isOrthogonalBelow_single_eStar a).mulVec (mem_partialUnitriangularGroup_of_mem_floorGroup hn)
      le_rfl
  intro k hk
  have h_fix : ((ν * n).val.val *ᵥ Pi.single (eStar a) (1 : A)) k =
      (n.val.val *ᵥ Pi.single (eStar a) (1 : A)) k := by
    rw [Subgroup.coe_mul, Units.val_mul, ← mulVec_mulVec]
    exact h_orth.congrBelow_mulVec hν k hk
  rw [sub_mulVec, sub_mulVec, Pi.sub_apply, Pi.sub_apply, h_fix]

/-- Let the Heisenberg element n = `heisenbergElem a t` have the parameters t = (ω, β) on floor a,
with ω extended by zero, and let τ = `element`. If (ν n - 1) e*_a / u has size i for some ν in
U_(<a) = `T.unipotentBelow a`, then ω / u and (β - τ ⟨ω, ω⟩) / u have size i. -/
lemma Size.mem_vecsOfSize_and_mem_ofSize_of_heisenbergElem {S : Size T} {u : Aˣ}
    {t : ({k : 𝔰.BesselIndex // a + 1 ≤ floorOf k} → A) × skewAdjoint A}
    (h_column : ∃ ν ∈ T.unipotentBelow a, u⁻¹.val • (fun k : 𝔰.BesselIndex ↦
      ((ν * heisenbergElem a t).val.val - 1) k (eStar a)) ∈ S.vecsOfSize i) :
    u⁻¹.val • inclMatrix A Subtype.val *ᵥ t.1 ∈ S.vecsOfSize i ∧
    u⁻¹ * (t.2.val - element * star (inclMatrix A Subtype.val *ᵥ t.1) ⬝ᵥ
      T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ t.1) ∈ S.ofSize i := by
  obtain ⟨ν, hν, h_short⟩ := h_column
  have h_floor : heisenbergElem (T := T) a t ∈ floorGroup a :=
    (heisenbergElem_mem_floorUnipotent a t).1
  refine mem_vecsOfSize_of_congrBelow_heisenbergElem (congrBelow_sub_one_mulVec h_floor hν) ?_
  rwa [mulVec_single_one]

namespace Gauge

/-- The set of vectors all of whose entries have size `j` for the gauge `Γ` is measurable. -/
lemma measurableSet_vecsOfSize {n : Type} [Fintype n] : MeasurableSet (Γ.vecsOfSize (n := n) j) :=
  .univ_pi' fun _ ↦ (Γ.isCompact_ofSize j).measurableSet

/-- If the isometry g is near at j for the place datum `F`, each vector e_a (`a : Fin 𝔰.ϱ`) with
a < j is balanced at g for the gauge `Γ` of `F` with exponent 5: some lift of e_a and some dual of
e_a are moved by g⁻¹ to vectors of size 5. -/
lemma isBalanced_of_isNear (h_near : F.IsNear j g) (ha : a < j) : Γ.IsBalanced g a 5 := by
  -- If `ξ g` lies in the box, take the lift `ξ⁻¹ e_a` and the dual `ξ⁻¹ e*_a`; read at `g`, they
  -- are columns of `(ξ g)⁻¹`.
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup j, ξ * g ∈ F.boxSet := h_near
  have h_size : Γ.HasMatrixSize 5 (ξ * g)⁻¹.val.val := (Γ.hasMatrixSize_boxSet h_box).inv
  have h_col (k : 𝔰.BesselIndex) : Γ.LengthLeAt g 5 (ξ⁻¹.val.val *ᵥ Pi.single k 1) := by
    intro i
    rw [mulVec_mulVec]
    simpa using h_size i k
  have h_orth : IsOrthogonalBelow a (Pi.single (eStar a) (1 : A) : 𝔰.BesselIndex → A) :=
    isOrthogonalBelow_single_eStar a
  have h_lift : CongrBelow a (Pi.single (inl a) 1) (ξ⁻¹.val.val *ᵥ Pi.single (inl a) 1) := by
    intro k hk
    simpa [Matrix.one_apply, Pi.single_apply] using
      mem_partialUnitriangularGroup.1 (inv_mem hξ) k (inl a) hk (.inl ⟨ha, ha⟩)
  have h_dual : (ξ⁻¹.val.val *ᵥ Pi.single (eStar a) (1 : A)) (eStar a) = 1 := by
    simpa using partialUnitriangularGroup_mulVec_eStar (inv_mem hξ) ha h_orth
  exact ⟨⟨_, h_lift, h_col (inl a)⟩, _, h_orth.mulVec (inv_mem hξ) ha.le, h_dual, h_col (eStar a)⟩

/-- Coordinates of a frame vector. Let g have size i for the gauge `Γ` of the place datum `F`, let σ
lie in G^(b) = `floorGroup b`, and let σ g be near at b + 1. Then `orbitPoint b σ`, the image under
σ⁻¹ of the frame vector number b, has size i + 6. Size i means that all entries lie in
`Γ.ofSize i`. -/
lemma orbitPoint_mem_vecsOfSize (hσ : σ ∈ floorGroup b) (hg : Γ.HasMatrixSize i g.val.val)
    (h_near : F.IsNear (b + 1) (σ * g)) : orbitPoint b σ ∈ Γ.vecsOfSize (i + 6) := by
  obtain ⟨ξ, hξ, h_box⟩ : ∃ ξ ∈ partialUnitriangularGroup (b + 1), ξ * (σ * g) ∈ F.boxSet := h_near
  intro k
  -- The vector is cut from a column of `σ⁻¹ * ξ⁻¹ = g * (ξ * (σ * g))⁻¹`, of size `i + 5 + 1`.
  have h_size : Γ.HasMatrixSize (i + 6) (σ⁻¹ * ξ⁻¹).val.val := by
    have h_eq : σ⁻¹ * ξ⁻¹ = g * (ξ * (σ * g))⁻¹ := by group
    rw [h_eq, Subgroup.coe_mul, Units.val_mul]
    exact hg.mul (Γ.hasMatrixSize_boxSet h_box).inv
  have h_col : orbitPoint b σ k =
      if floorOf k < b then 0 else (σ⁻¹ * ξ⁻¹).val.val k (𝔰.besselFrame b) := by
    rw [orbitPoint, mulVec_single_one]
    exact floorGroup_apply_besselFrame (inv_mem hσ) (inv_mem hξ) k
  rw [h_col]
  split_ifs
  · simp [zero_one_mem_ofSize]
  · exact h_size k (𝔰.besselFrame b)

/-- The set of close positions of the gauge `Γ` of the place datum `F`, the positions z for which
(z - 1) / M has size 1 with M = `F.levelUnit`, is measurable. -/
lemma measurableSet_positionsOfSize : MeasurableSet Γ.positionsOfSize := by
  have h_positions : MeasurableSet F.positions := F.isCompact_boxSet_and_measurableSet_positions.2
  have h_size : MeasurableSet {z : T.G | Γ.HasMatrixSize 1 (F.levelUnit⁻¹.val • (z.val.val - 1))} :=
    (Γ.isCompact_ofSize 1).matrix.measurableSet.preimage (by fun_prop)
  exact h_positions.inter h_size

end Gauge

end New.Floors

namespace New.Floors.PlaceData

open MeasureTheory Measure ProbabilityTheory FloorGroups Set

variable {R ι : Type} {𝔰 : Shape} [CommRing R] [StarRing R] [TopologicalSpace R] [MeasureSpace R]
  [Place R] [Fintype ι] [DecidableEq ι] {m j l : ℕ} {T : 𝔰.Form R} [IsHermitianUnit T.splitGram]
  {F : PlaceData ι T m} {g y : T.G} {s : T.G} {k : T.G → T.G → ℂ} {d : T.G}

namespace IsPairingKernel

/-! ### The averaged kernel -/

/-- For a pairing kernel `k`, the correlation from floor `l` on is jointly strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_partialCorrelation (hk : F.IsPairingKernel j k d) :
    StronglyMeasurable ↿(F.partialCorrelation l k) := by
  have h_meas : Measurable ↿k := hk.measurable
  exact .integral_prod_right (by fun_prop)

/-- If `k` is a pairing kernel at floor `j`, it is one at every floor `l ≥ j`, with the same `d`. -/
lemma mono (hk : F.IsPairingKernel j k d) (h : j ≤ l) : F.IsPairingKernel l k d :=
  { hk with conj_eq_self := fun s hs ↦ hk.conj_eq_self s (floorGroup_anti h hs) }

/-- For a pairing kernel `k`, the integral over the floors from `l` on that defines
`F.partialCorrelation l k g y` converges absolutely. -/
lemma integrable_quotientMeasureFrom (hk : F.IsPairingKernel j k d) (l : ℕ) (g y : T.G) :
    Integrable (fun x : T.G ↦ k (x * g) (x * y)) (F.quotientMeasureFrom l) := by
  obtain ⟨c, hc, h_bound⟩ :
      ∃ c < ⊤, ∀ g y : T.G, ∫⁻ x : T.G, ‖k (x * g) (x * y)‖ₑ ∂F.quotientMeasureFrom l ≤ c :=
    hk.exists_lintegral_le l
  have h_meas : Measurable ↿k := hk.measurable
  exact ⟨Measurable.aestronglyMeasurable (by fun_prop), (h_bound g y).trans_lt hc⟩

/-- For a pairing kernel `k`, the function x ↦ k(x g, x y) is integrable for the convolution of the
measure of the floors from `l + 1` on with the measure of floor `l`. -/
lemma integrable_quotientMeasureFrom_mconv_floorMeasure (hk : F.IsPairingKernel j k d) (l : ℕ)
    (g y : T.G) :
    Integrable (fun x : T.G ↦ k (x * g) (x * y))
      (F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l) := by
  rw [← F.quotientMeasureFrom_eq_succ_mconv]
  exact hk.integrable_quotientMeasureFrom l g y

/-- For a pairing kernel `k`, the correlation `F.partialCorrelation (l + 1) k (σ * g) (σ * y)` from
floor `l + 1` on is integrable in σ for the measure `F.floorMeasure l` of floor `l`. -/
lemma integrable_partialCorrelation_succ (hk : F.IsPairingKernel j k d) :
    Integrable (fun σ : T.G ↦ F.partialCorrelation (l + 1) k (σ * g) (σ * y))
      (F.floorMeasure l) := by
  have h_prod : Integrable (fun p : T.G × T.G ↦ k (p.1 * p.2 * g) (p.1 * p.2 * y))
      ((F.quotientMeasureFrom (l + 1)).prod (F.floorMeasure l)) :=
    (hk.integrable_quotientMeasureFrom_mconv_floorMeasure l g y).comp_measurable measurable_mul
  simp only [partialCorrelation, ← mul_assoc]
  exact h_prod.integral_prod_right

/-- For a pairing kernel `k`, the correlation `F.partialCorrelation l k g y` from floor `l` on is
the integral of `F.partialCorrelation (l + 1) k (σ * g) (σ * y)` in σ for the measure
`F.floorMeasure l` of floor `l`. -/
lemma partialCorrelation_eq_integral_floorMeasure (hk : F.IsPairingKernel j k d) :
    F.partialCorrelation l k g y =
      ∫ σ : T.G, F.partialCorrelation (l + 1) k (σ * g) (σ * y) ∂F.floorMeasure l := by
  -- `F.quotientMeasureFrom l` is `F.quotientMeasureFrom (l + 1)` convolved with `F.floorMeasure l`;
  -- the claim is Fubini's theorem on the product of the two.
  have h_int : Integrable (fun x : T.G ↦ k (x * g) (x * y))
      (F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l) :=
    hk.integrable_quotientMeasureFrom_mconv_floorMeasure l g y
  calc F.partialCorrelation l k g y
    _ = ∫ x : T.G, k (x * g) (x * y) ∂(F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l) := by
      rw [partialCorrelation, F.quotientMeasureFrom_eq_succ_mconv (l := l)]
    _ = ∫ x : T.G, ∫ σ : T.G, k (x * σ * g) (x * σ * y)
          ∂F.floorMeasure l ∂F.quotientMeasureFrom (l + 1) := integral_mconv h_int
    _ = ∫ σ : T.G, ∫ x : T.G, k (x * σ * g) (x * σ * y)
          ∂F.quotientMeasureFrom (l + 1) ∂F.floorMeasure l :=
      integral_integral_swap (h_int.comp_measurable measurable_mul)
    _ = ∫ σ : T.G, F.partialCorrelation (l + 1) k (σ * g) (σ * y) ∂F.floorMeasure l := by
      simp only [partialCorrelation, mul_assoc]

/-- For a pairing kernel `k` with element `d` at any floor `j`, the correlation
`F.partialCorrelation l k g y` from floor `l` on is an absolutely convergent integral: that of
`F.partialCorrelation (l + 1) k (σ * g) (σ * y)` over σ against θ_l = `F.floorMeasure l`. -/
lemma partialCorrelation_eq_integral_succ (hk : F.IsPairingKernel j k d) :
    Integrable (fun σ : T.G ↦ F.partialCorrelation (l + 1) k (σ * g) (σ * y)) (F.floorMeasure l) ∧
    F.partialCorrelation l k g y =
      ∫ σ : T.G, F.partialCorrelation (l + 1) k (σ * g) (σ * y) ∂F.floorMeasure l :=
  ⟨hk.integrable_partialCorrelation_succ, hk.partialCorrelation_eq_integral_floorMeasure⟩

/-- For a pairing kernel `k`, the modulus of the correlation from floor `l` on is at most
`F.pivotL1Norm l k g y`, the integral over floor `l` of the modulus of the correlation from floor
`l + 1` on. -/
lemma enorm_partialCorrelation_le (hk : F.IsPairingKernel j k d) :
    ‖F.partialCorrelation l k g y‖ₑ ≤ F.pivotL1Norm l k g y := by
  rw [hk.partialCorrelation_eq_integral_floorMeasure]
  exact enorm_integral_le_lintegral_enorm _

/-- Let `k` satisfy `F.IsPairingKernel j k d` with `j ≤ l`. Then `F.partialCorrelation l k`, the
integral of k(x g, x y) in x for `F.quotientMeasureFrom l`, is unchanged when both arguments are
left translated by the same `s` in R^(l) ∩ G^(j). -/
lemma partialCorrelation_mul_left (hk : F.IsPairingKernel j k d) (hl : j ≤ l)
    (hs : s ∈ partialUnitriangularGroup l ⊓ floorGroup j) :
    F.partialCorrelation l k (s * g) (s * y) = F.partialCorrelation l k g y := by
  -- Descending induction on the floor `l`.
  induction h_floor : 𝔰.ϱ + 2 - l generalizing l s g y with
  | zero =>
    -- Here no averaging is left; `s` lies in `T.besselU = unipotentBelow 𝔰.n` and commutes with
    -- `d`, so the character in `hk.equivariance` is `1`.
    obtain ⟨hs_unitri, hs_floor⟩ : s ∈ partialUnitriangularGroup l ∧ s ∈ floorGroup j :=
      Subgroup.mem_inf.1 hs
    have hs_U : s ∈ T.besselU := partialUnitriangularGroup_add_two_eq_besselU.le
      (partialUnitriangularGroup_anti (by lia) hs_unitri)
    have hs_N : s ∈ unipotentBelow 𝔰.n := by rwa [unipotentBelow_eq_besselU 𝔰.ϱ.le_succ]
    have h_law : F.partialCorrelation (𝔰.n + 1) k (s * g) (s * y) = F.partialCorrelation (𝔰.n + 1) k
      g y := by
      simpa [hk.conj_eq_self s hs_floor] using hk.equivariance hs_N hs_N g y
    -- from floor `l` on, as from floor `𝔰.n + 1 = 𝔰.ϱ + 2` on, the measure is the unit mass at `1`
    simpa [partialCorrelation, descConv, h_floor] using h_law
  | succ i ih =>
    -- `F.partialCorrelation l` is the integral of `Φ`, which is invariant by induction, so by
    -- `lintegral_floorMeasure_mul_right` the translate of `Φ` by `s` has the law of `Φ`.
    let Φ (σ : T.G) : ℂ := F.partialCorrelation (l + 1) k (σ * g) (σ * y)
    have h_inv : ∀ u ∈ partialUnitriangularGroup (l + 1) ⊓ floorGroup j, ∀ σ : T.G,
      Φ (u * σ) = Φ σ := by
      intro u hu σ
      simp only [Φ, mul_assoc]
      exact ih (hl.trans l.le_succ) hu (by lia)
    have h_law : IdentDistrib (fun σ ↦ Φ (σ * s)) Φ (F.floorMeasure l) (F.floorMeasure l) := by
      refine ⟨by fun_prop, by fun_prop, ext_of_lintegral _ fun φ hφ ↦ ?_⟩
      rw [lintegral_map hφ (by fun_prop), lintegral_map hφ (by fun_prop)]
      exact lintegral_floorMeasure_mul_right (f := fun σ ↦ φ (Φ σ)) (floorGroup_anti hl)
        (fun u hu σ ↦ congrArg φ (h_inv u hu σ)) hs
    simpa [hk.partialCorrelation_eq_integral_floorMeasure (l := l), Φ, mul_assoc] using
      h_law.integral_eq

end IsPairingKernel

end New.Floors.PlaceData

end
