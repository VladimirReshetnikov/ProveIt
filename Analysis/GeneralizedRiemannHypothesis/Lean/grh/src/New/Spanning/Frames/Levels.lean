import Lib.DiscreteSeries.Bruhat.FloorMeasures
import New.Spanning.Frames.Lengths

/-!
# Place data, floor measures and depth

A place datum `F` fixes a unit M, a compact set K and a basis adapted to the frame. The group
measure is built floor by floor: floor `l ≤ ϱ` chooses the frame vector f_l on its quadric and an
element of the Heisenberg group along it, and floor ϱ + 1 carries the measure of H. The letters
Y^(l), K and M are those of the head of `New.Spanning.Frames.Lengths`.

Notions from other files:
* G = `T.G` is the unitary group of `T.splitGram`, a hermitian form with ϱ = `𝔰.ϱ` hyperbolic pairs
  e_a, e*_a; its basis vectors are indexed by `𝔰.BesselIndex`, and n = `𝔰.n` is ϱ + 1.
* G^(l) = `floorGroup l` is the group of isometries that fix the basis vectors of floor below l;
  H = `besselH` is G^(ϱ+1).
* R^(l) = `partialUnitriangularGroup l` is the group of isometries that are unitriangular on the
  first l frame vectors, and U = `besselU` is the Bessel unipotent group.
* `orbitPoint b g` is the vector g⁻¹ f_b, where f_b is the frame vector of floor b, and
  `F.floorQuadricMeasure b` is the measure on the quadric through f_b.
* η_l = `heisenbergMeasure l` is the measure of the Heisenberg group of floor l, and `weylLaw l` is
  a measure carried by the inverse Weyl elements of floor l.

## Main definitions and results

* `New.Floors.PlaceData`, `New.Floors.PlaceData.floorMeasure`, `New.Floors.PlaceData.groupMeasure`:
  the data and the measures.
* `New.Floors.PlaceData.IsNear`, `New.Floors.PlaceData.IsStable`,
  `New.Floors.PlaceData.stableProducts`, `New.Floors.PlaceData.depth`,
  `New.Floors.PlaceData.depthWeight`: points near K, stable vectors, their products with e_a, depth
  and the weight.
* `New.Floors.PlaceData.measurePreserving_orbitPoint`: a floor measure maps to the measure of the
  quadric.
* `New.Floors.PlaceData.partialGroupMeasure_mconv_dirac`,
  `New.Floors.PlaceData.lintegral_partialGroupMeasure_weylElem_inv_mul`: invariance on the right,
  and invariance under a Weyl element on the left for the lower floors, for integrals of functions
  fixed on the left by G^(j), when the group measure is Haar.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

section LevelGauge

open Matrix MeasureTheory Measure BesselIndex ENNReal Fintype FloorGroups Place TraceOne Function
  Filter

variable {A : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A] [P : Place A]
  (ι : Type) [Fintype ι] [DecidableEq ι] {𝔰 : Shape} (T : 𝔰.Form A) (m : ℕ)
  [IsHermitianUnit T.splitGram] {l i j : ℕ}

/-!
## Place data, floor measures and their invariance

`New.Floors.descConv σ a i` is the convolution `σ (a + i - 1) ∗ ⋯ ∗ σ a`, and `η_l` is
`New.Floors.Place.heisenbergMeasure l`.
-/

/-- The data of a place: a basis of hyperbolic pairs and orthonormal vectors, the measures of the
top floor and of H, the level M (the field `levelUnit`), the close pairs of vectors, the compact set
K of the group and the set of positions. -/
structure PlaceData extends HyperbolicBasis ι T m where
  /-- The measure of the top floor, on G^(ϱ) = `floorGroup 𝔰.ϱ`. -/
  topFloorMeasure : Measure T.G
  /-- A right invariant measure carried by H = `besselH`; see
  `measureH_mem_and_invariant_and_le_one`. -/
  measureH : Measure T.G
  /-- The level M, a unit by which differences of vectors and frequencies are divided. -/
  levelUnit : Aˣ
  /-- The close pairs (ω₁, ω₂) of vectors. In the place data that are used they are the pairs with
  |ω₁|² + |ω₂|² < 1 at a real place, and those with ω₁ in the lattice and ω₂ ≡ ω₁ modulo M at the
  finite places. -/
  closePairs : Set ((𝔰.BesselIndex → A) × (𝔰.BesselIndex → A))
  /-- The compact set K in the unitary group G. -/
  boxSet : Set T.G
  /-- The positions: the elements of G by which the second point of a pair differs from the
  first. -/
  positions : Set T.G
  /-- The measure `topFloorMeasure` is s-finite. -/
  [sFinite_topFloorMeasure : SFinite topFloorMeasure]
  /-- The measure of H is s-finite. -/
  [sFinite_measureH : SFinite measureH]
  /-- The measure of H is not zero. -/
  [neZero_measureH : NeZero measureH]
  /-- `topFloorMeasure` is carried by G^(ϱ), and σ ↦ σ⁻¹ f_ϱ maps it to the measure of the top
  quadric. -/
  topFloorMeasure_mem_and_map_eq :
      (∀ᵐ x : T.G ∂topFloorMeasure, x ∈ floorGroup 𝔰.ϱ) ∧
      topFloorMeasure.map (orbitPoint 𝔰.top) = toHyperbolicBasis.floorQuadricMeasure 𝔰.top
  /-- The measure of H is carried by H, is invariant under right translation by H, and for every g
  gives mass at most 1 to the h with h g ∈ U K. -/
  measureH_mem_and_invariant_and_le_one :
      (∀ᵐ x : T.G ∂measureH, x ∈ besselH) ∧
      (∀ s ∈ besselH, measureH ∗ₘ dirac s = measureH) ∧
      ∀ g : T.G, measureH {h : T.G | ∃ u ∈ besselU, u * (h * g) ∈ boxSet} ≤ 1
  /-- The level is fixed by the involution. -/
  star_levelUnit : star levelUnit.1 = levelUnit
  /-- The set of close pairs is open, contains 0 and has compact closure. -/
  isOpen_closePairs_and_zero_mem_and_isCompact_closure :
    IsOpen closePairs ∧ 0 ∈ closePairs ∧ IsCompact (closure closePairs)
  /-- The set K is compact and the set of positions is measurable. -/
  isCompact_boxSet_and_measurableSet_positions : IsCompact boxSet ∧ MeasurableSet positions

variable {ι T m} {ν ρ : Measure T.G} [SFinite ν] [SFinite ρ]
  {s : T.G} {S : Subgroup T.G} {f Φ : T.G → ℝ≥0∞} (F : PlaceData ι T m) (b : Fin 𝔰.n)

namespace PlaceData

attribute [instance] sFinite_topFloorMeasure sFinite_measureH neZero_measureH

/-- The measure `F.topFloorMeasure` of the top floor is carried by G^(ϱ) = `floorGroup 𝔰.ϱ`. -/
lemma ae_topFloorMeasure_mem_floorGroup (F : PlaceData ι T m) : ∀ᵐ x : T.G ∂F.topFloorMeasure,
  x ∈ floorGroup 𝔰.ϱ :=
  F.topFloorMeasure_mem_and_map_eq.left

/-- The map `orbitPoint 𝔰.top`, σ ↦ σ⁻¹ f_ϱ with f_ϱ = z the last frame vector, carries
`F.topFloorMeasure`, the measure of the top floor that is part of the place data `F`, to
`F.floorQuadricMeasure 𝔰.top`, the measure on the top quadric. -/
lemma map_orbitPoint_topFloorMeasure (F : PlaceData ι T m) :
    F.topFloorMeasure.map (orbitPoint 𝔰.top) = F.floorQuadricMeasure 𝔰.top :=
  F.topFloorMeasure_mem_and_map_eq.right

/-- The measure `F.measureH` is carried by H = `besselH`, the fixer of the hyperbolic pairs and the
last frame vector. -/
lemma ae_measureH_mem_besselH (F : PlaceData ι T m) : ∀ᵐ x : T.G ∂F.measureH, x ∈ besselH :=
  F.measureH_mem_and_invariant_and_le_one.left

/-- The measure `F.measureH` is invariant under right translation by H = `besselH`. -/
lemma measureH_mconv_dirac (F : PlaceData ι T m) {s : T.G} (hs : s ∈ besselH) :
    F.measureH ∗ₘ dirac s = F.measureH := by
  obtain ⟨-, h_right, -⟩ := F.measureH_mem_and_invariant_and_le_one
  exact h_right s hs

/-- For every g, the h with h g ∈ U K, that is u h g ∈ K for some u in U, have mass at most 1 for
`F.measureH`. Here U = `besselU` is the Bessel unipotent group and K = `F.boxSet`. -/
lemma measureH_setOf_mul_mem_boxSet_le_one (g : T.G) :
    F.measureH {h : T.G | ∃ u ∈ besselU, u * (h * g) ∈ F.boxSet} ≤ 1 := by
  obtain ⟨-, -, h_mass⟩ := F.measureH_mem_and_invariant_and_le_one
  exact h_mass g

/-- The measure θ_l of floor l on G^(l). For l ≤ ϱ the map `orbitPoint l` carries it to the quadric
measure `F.floorQuadricMeasure l`, and for l < ϱ it lives on the big cell. Floor n = ϱ + 1 carries
the measure of H, and higher floors a unit mass at 1. -/
def floorMeasure (l : ℕ) : Measure T.G :=
  if l < 𝔰.ϱ then weylLaw l ∗ₘ heisenbergMeasure l
  else if l = 𝔰.ϱ then F.topFloorMeasure
  else if l = 𝔰.n then F.measureH
  else dirac 1

/-- Every floor measure is s-finite. -/
instance : SFinite (F.floorMeasure l) := by
  fun_cases floorMeasure
  all_goals infer_instance

/-- `partialGroupMeasure l i` convolves the Heisenberg and floor measures of the i floors from l on.
For l + i = ϱ + 2 it is invariant under right translation by G^(l)
(`partialGroupMeasure_mconv_dirac`). -/
abbrev partialGroupMeasure : ℕ → ℕ → Measure T.G :=
  descConv fun a : ℕ ↦ heisenbergMeasure a ∗ₘ F.floorMeasure a

/-- The measure (η_{ϱ+1}∗θ_{ϱ+1}) ∗ ⋯ ∗ (η₀∗θ₀) on the unitary group, the convolution over all
floors, where η_a = `heisenbergMeasure a` and θ_a = `F.floorMeasure a`. -/
abbrev groupMeasure : Measure T.G := F.partialGroupMeasure 0 (𝔰.ϱ + 2)

/-- The convolution θ_(ϱ+1) ∗ ⋯ ∗ θ_l of the floor measures from l on. It serves to integrate
functions on G^(l) that are left invariant under U ∩ G^(l). -/
@[simp]
abbrev quotientMeasureFrom (l : ℕ) : Measure T.G := descConv F.floorMeasure l (𝔰.ϱ + 2 - l)

/-- A point g is near at j if R^(j) g meets K = `F.boxSet`, where R^(j) =
`partialUnitriangularGroup j`. -/
def IsNear (j : ℕ) (g : T.G) : Prop := ∃ ξ ∈ T.partialUnitriangularGroup j, ξ * g ∈ F.boxSet

/-- The rank 2 m + 2 of a block of orthonormal basis vectors in which the equation of a quadric is
solved. -/
abbrev blockRank (_ : PlaceData ι T m) : ℕ := 2 * m + 2

/-- The indices of the orthonormal basis vectors that remain when two blocks are set aside. These
vectors span the space X'. -/
abbrev FreeIndex : Type := Fin (card ι - 2 * F.blockRank)

/-- The index in ι of a basis vector of X'. These are the first `card ι - 2 * F.blockRank`
orthonormal basis vectors in a fixed numbering of ι. -/
def freeIndex (i : F.FreeIndex) : ι :=
  (equivFin ι).symm (i.castLE (Nat.sub_le (card ι) (2 * F.blockRank)))

/-- The matrix whose columns are the basis vectors of X'; it embeds X' into the space. For a vector
y, we write y_X for the vector of the products of these columns with y. -/
abbrev orthonormalPart : Matrix 𝔰.BesselIndex F.FreeIndex A :=
  fromRows 0 ((F.basisMatrix.toCols₂.toCols₂.toCols₁.submatrix id F.freeIndex).fromRows 0)

/-- A vector ω is short from g and g' if (g⁻¹ ω, g'⁻¹ ω) is a close pair. -/
abbrev IsShortFrom (g g' : T.G) (ω : 𝔰.BesselIndex → A) : Prop :=
  (g⁻¹.val.val *ᵥ ω, g'⁻¹.val.val *ᵥ ω) ∈ F.closePairs

/-- The class of ω in Y^(l) is stable at g and g', with ω as its lift at g: the vector ω is
orthogonal to the e_b, b < l, and (g⁻¹ ω, g'⁻¹ ω') is a close pair for some ω' that agrees with ω
at all indices k with l ≤ `level k` (for l ≤ ϱ, another lift of the class). -/
def IsStable (l : ℕ) (g g' : T.G) (ω : 𝔰.BesselIndex → A) : Prop :=
  IsOrthogonalBelow l ω ∧ ∃ ω' : 𝔰.BesselIndex → A,
    CongrBelow l ω ω' ∧ (g⁻¹.val.val *ᵥ ω, g'⁻¹.val.val *ᵥ ω') ∈ F.closePairs

/-- The set 𝔡_a at the points x and x y: the products ⟨e_a, ω⟩ with the vectors ω of Y^(a) that are
stable at x and x y. In the place data that are used it is a disc at a real place, and at the finite
places a fractional ideal, contained in the integers if x is near at a + 1. -/
def stableProducts (a : Fin 𝔰.ϱ) (x y : T.G) : Set A :=
  (fun ω : 𝔰.BesselIndex → A ↦ ω (eStar a)) ''
    {ω : 𝔰.BesselIndex → A | F.IsStable a x (x * y) ω}

/-- The depth of the vector e_a at the points x and x y: the inverse of the volume of 𝔡_a. In the
place data that are used it is as follows. At the finite places it is the index of the ideal 𝔡_a if
x is near at a + 1 (`New.Floors.IntegralPlace.IsLargeLatticeData.exists_ideal_depth_eq`). At a real
place it is 1 / π times the infimum of |ζ|² at x plus |ζ|² at x y over the duals ζ of e_a in Y^(a)
(`New.Floors.RealPlaceSizes.depth_eq`). -/
def depth (a : Fin 𝔰.ϱ) (x y : T.G) : ℝ≥0∞ := (volume (F.stableProducts a x y))⁻¹

/-- The exponent s of the depths in `depthWeight`: the rank of X' minus (3 n + 1 + m). -/
abbrev volumeExponent : ℕ := card F.FreeIndex - (3 * 𝔰.n + 1 + m)

/-- The weight of length j at the points x and x y: the product of the powers depth^(-s),
s = `F.volumeExponent`, over the first j vectors e_a. -/
def depthWeight (j : ℕ) (x y : T.G) : ℝ≥0∞ :=
  ∏ a : Fin 𝔰.ϱ with a.val < j, (F.depth a x y)⁻¹ ^ F.volumeExponent

/-- The common vectors: the ω in X' that are killed by the rows of v and are short from g
and g z. -/
def commonVectors (g z : T.G) (v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A) : Set (F.FreeIndex → A) :=
  {ω : F.FreeIndex → A | v *ᵥ ω = 0 ∧ F.IsShortFrom g (g * z) (F.orthonormalPart *ᵥ ω)}

/-- The numbers (⟨ω₁, ω'₁⟩ - ⟨ω₂, ω'₂⟩) / M for two pairs (ω₁, ω₂), (ω'₁, ω'₂) in `closePairs`. In
the place data that are used they lie in the disc of radius 1 at a real place and are integral at
the finite places. -/
def productDifferences : Set A :=
  {c : A | ∃ z ∈ F.closePairs, ∃ z' ∈ F.closePairs,
    c = F.levelUnit⁻¹ * (star z.1 ⬝ᵥ T.splitGram *ᵥ z'.1 - star z.2 ⬝ᵥ T.splitGram *ᵥ z'.2)}

/-- The function φ on X' controls the products with the set W of vectors, and its s-th power,
s = `F.volumeExponent`, has integral at most Λ^(99 n (j+1)) over the vectors of size j for the
scale `S`. -/
structure IsCommonBound (S : Size T) (Λ : ℝ≥0∞) (W : Set (F.FreeIndex → A))
    (φ : (F.FreeIndex → A) → ℝ≥0∞) : Prop where
  /-- The function φ is measurable. -/
  measurable : Measurable φ
  /-- φ(u) bounds 1 / vol ⟨u, W⟩. -/
  inv_volume_le (u : F.FreeIndex → A) :
    (volume ((fun ω : F.FreeIndex → A ↦ star u ⬝ᵥ ω) '' W))⁻¹ ≤ φ u
  /-- φ(u) bounds the volume of the numbers c with ⟨c u, W⟩ inside `productDifferences`. -/
  volume_le (u : F.FreeIndex → A) :
    volume {c : A | ∀ ω ∈ W, star (c • u) ⬝ᵥ ω ∈ F.productDifferences} ≤ φ u
  /-- The integral of φ^s over the vectors of size j is at most Λ^(99 n (j+1)). -/
  lintegral_le (j : ℕ) :
    ∫⁻ u : F.FreeIndex → A in S.vecsOfSize j, φ u ^ F.volumeExponent ≤ Λ ^ (99 * 𝔰.n * (j + 1))

/-- The number |g|^(r+1/2), where r = k + 1 + 2 (ϱ - (l + 1)) is the rank of the vector part of the
Heisenberg group of floor l; by default g is the level M. -/
def floorModulus (l : ℕ) (g := F.levelUnit) : ℝ≥0∞ :=
  P.modulus g ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1))) * P.modulus g ^ (2⁻¹ : ℝ)

variable {F}

/-- The enumeration of the basis of V_a, the span of the basis vectors of floor at least a: first
the hyperbolic pair e_a, e*_a, then the basis vectors of the higher floors. -/
def floorIndexEnum (a : Fin 𝔰.ϱ) :
    Fin 2 ⊕ {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → 𝔰.BesselIndex :=
  ![.inl a, eStar a] ⊕ᵥ Subtype.val

/-- The Gram matrix of the basis vectors of floor at least l. -/
def upperGram (l : ℕ) :
    Matrix {i : 𝔰.BesselIndex // l ≤ floorOf i} {i : 𝔰.BesselIndex // l ≤ floorOf i} A :=
  T.splitGram.submatrix Subtype.val Subtype.val

/-- The enumeration `floorIndexEnum a` of the basis of V_a has no repetitions. -/
lemma floorIndexEnum_injective (a : Fin 𝔰.ϱ) : Injective (floorIndexEnum a) := by
  -- the only coincidences to exclude are those of `e_a`, `e*_a` with a higher pair
  suffices (∀ c : Fin 𝔰.ϱ, a < c → a ≠ c) ∧ ∀ c : Fin 𝔰.ϱ, a < c → c ≠ a by
    simpa [floorIndexEnum, Injective] using this
  exact ⟨fun c hc ↦ hc.ne, fun c hc ↦ hc.ne'⟩

/-- The enumeration `floorIndexEnum a` lists exactly the basis indices of floor at least a. -/
lemma mem_range_floorIndexEnum (a : Fin 𝔰.ϱ) (i : 𝔰.BesselIndex) :
    i ∈ Set.range (floorIndexEnum a) ↔ a.val ≤ floorOf i := by
  have h_le (c : Fin 𝔰.ϱ) : c = a ∨ a < c ↔ a ≤ c := by rw [le_iff_eq_or_lt, eq_comm]
  obtain c | (k | z) | c := i
  · -- `e_c` is listed if `c = a` or `a < c`
    simp [floorIndexEnum, h_le]
  · -- the middle indices other than `z` have floor `n`
    have ha : a.val ≤ 𝔰.n := by grind
    simp [floorIndexEnum, ha]
  · -- `z` has floor ϱ
    simp [floorIndexEnum]
  · -- `e*_c` is listed if `c = a` or `a < c`
    simp [floorIndexEnum, h_le]

omit [IsHermitianUnit T.splitGram] [TopologicalSpace A] [MeasureSpace A] [Place A] in
/-- In the basis `floorIndexEnum a` of V_a, the form `T.splitGram` is a hyperbolic plane plus the
form `upperGram (a + 1)` on the higher floors. -/
lemma gram_inclMatrix_floorIndexEnum (a : Fin 𝔰.ϱ) :
    (inclMatrix A (floorIndexEnum a))ᴴ * T.splitGram * inclMatrix A (floorIndexEnum a) =
      planeSumGram (upperGram (T := T) (a + 1)) := by
  rw [gram_inclMatrix]
  -- the pair of floor `a` is orthogonal to the higher pairs
  suffices (∀ c : Fin 𝔰.ϱ, a < c → a = c → (1 : A) = 0) ∧
      ∀ c : Fin 𝔰.ϱ, a < c → c = a → (1 : A) = 0 by
    simpa [floorIndexEnum, upperGram, ← ext_iff] using this
  exact ⟨fun c hc h ↦ absurd h hc.ne, fun c hc h ↦ absurd h hc.ne'⟩

/-- For a < ϱ, the measure `F.floorQuadricMeasure a.castSucc` on the quadric h(v, v) = 0 of V_a can
be computed in the basis `floorIndexEnum a`. It is the image, under extension by zero, of the
measure `quadricMeasure` with parameter 0 of a hyperbolic plane plus the form `upperGram (a + 1)` on
the higher floors. -/
lemma floorQuadricMeasure_castSucc_eq_map (a : Fin 𝔰.ϱ) :
    F.floorQuadricMeasure a.castSucc =
      (quadricMeasure (upperGram (T := T) (a + 1)) 0).map
        (inclMatrix A (floorIndexEnum a) *ᵥ ·) := by
  -- Disintegrations of `floorVolume a` along `h(v, v)` are unique, and both sides are the member
  -- at `h(e_a, e_a) = 0` of such a disintegration.
  let E : Matrix 𝔰.BesselIndex (Fin 2 ⊕ {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}) A :=
    inclMatrix A (floorIndexEnum a)
  have h_left : Eᴴ * E = 1 := by
    simpa [submatrix_one _ (floorIndexEnum_injective a)] using
      gram_inclMatrix (A := A) (floorIndexEnum a) 1
  have h_vol : volume.map (E *ᵥ ·) = floorVolume a.castSucc :=
    map_inclMatrix_eq_floorVolume _ (floorIndexEnum_injective a) (mem_range_floorIndexEnum a)
  have h_herm : (upperGram (T := T) (a + 1)).IsHermitian :=
    IsHermitian.submatrix IsHermitianUnit.conjTranspose_eq _
  have h_dis :
      IsDisintegration (volume.map (E *ᵥ ·)) T.splitGram fun β : skewAdjoint A ↦
        (quadricMeasure (upperGram (T := T) (a + 1)) β).map (E *ᵥ ·) :=
    (isDisintegration_quadricMeasure (T := upperGram (T := T) (a + 1)) h_herm).map
      (gram_inclMatrix_floorIndexEnum a) h_left
  have h_zero :
      skewUnitMul (T.splitGram (𝔰.besselFrame a.castSucc) (𝔰.besselFrame a.castSucc)) = 0 := by
    ext
    simp
  rw [← h_zero]
  exact (F.isDisintegration_floorVolume _ h_vol).unique h_dis

/-- Let a < ϱ, let t be a unit, u a vector on the floors above a and β skew. The point ((t, t u), β)
of the chart `flatChart` of the quadric h(v, v) = 0 for a hyperbolic plane plus `upperGram (a + 1)`
is sent by `inclMatrix A (floorIndexEnum a)` to the image of e_a under the product of the Heisenberg
element `heisenbergElem a (u, β)` and the Weyl element `floorWeyl a t`. -/
lemma inclMatrix_mulVec_flatChart_eq_heisenbergElem_mulVec (a : Fin 𝔰.ϱ) (t : Aˣ)
    (u : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) (β : skewAdjoint A) :
    inclMatrix A (floorIndexEnum a) *ᵥ
        flatChart (upperGram (T := T) (a + 1)) 0 ((t, t.val • u), β) =
      (heisenbergElem (T := T) a (u, β)).val.val *ᵥ
        (floorWeyl a t.val : T.G).val.val *ᵥ Pi.single (.inl a) 1 := by
  have h_weyl : (floorWeyl a t.val : T.G).val.val *ᵥ Pi.single (.inl a) 1 =
      Pi.single (eStar a) t.val := by
    ext i
    simp [floorWeyl, weylOn, level, ← Pi.single_apply, col_apply']
  -- `c = h(u, u)`, written with the Gram matrix of the higher floors or after extension by zero
  set c : A := star u ⬝ᵥ upperGram (T := T) (a + 1) *ᵥ u with hc
  have h_form : star (inclMatrix A Subtype.val *ᵥ u) ⬝ᵥ T.splitGram *ᵥ inclMatrix A Subtype.val *ᵥ u
      = c := by
    rw [hc, upperGram, ← gram_inclMatrix, star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec]
  -- the coordinates of the chart point, where `h(t u, t u) = t̄ t c`
  have h_chart : flatChart (upperGram (T := T) (a + 1)) 0 ((t, t.val • u), β) =
      ![(β - element * c) * t, t] ⊕ᵥ t.val • u := by
    have h_cancel : Ring.inverse (star t.val) * star t.val = 1 :=
      Ring.inverse_mul_cancel _ t.isUnit.star
    have h_scale : star (t.val • u) ⬝ᵥ upperGram (T := T) (a + 1) *ᵥ t.val • u =
        star t.val * (t * c) := by
      simp [mulVec_smul, hc, mul_left_comm]
    rw [flatChart, h_scale]
    congr 2
    rw [ZeroMemClass.coe_zero]
    linear_combination (-element * t * c) * h_cancel
  have h_incl (x y : A) (w : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A) :
      inclMatrix A (floorIndexEnum a) *ᵥ (![x, y] ⊕ᵥ w) =
        Pi.single (eStar a) y + inclMatrix A Subtype.val *ᵥ w + x • Pi.single (.inl a) 1 := by
    ext i
    simp [floorIndexEnum, inclMatrix, mulVec_apply_eq_sum, Pi.single_apply, Matrix.one_apply,
      add_comm, add_assoc]
    -- the two sums differ only in their `Fintype` instances
    congr!
  rw [h_chart, h_incl, mulVec_smul, h_weyl, heisenbergElem_mulVec, h_form]
  simp [inclMatrix_val_mulVec, ↓splitGram_col]

/-- Let f be the b-th vector of the frame (e_0, …, e_{ϱ-1}, z) = `𝔰.besselFrame`. The map
`orbitPoint b`, σ ↦ σ⁻¹ f, carries the measure `F.floorMeasure b` on the isometries fixing the basis
vectors of floor below b to the measure `F.floorQuadricMeasure b` on the quadric h(v, v) = h(f, f)
in the span of the other basis vectors. -/
lemma measurePreserving_orbitPoint {F : PlaceData ι T m} (b : Fin 𝔰.n) :
    MeasurePreserving (orbitPoint b) (F.floorMeasure b) (F.floorQuadricMeasure b) := by
  refine ⟨by fun_prop, b.lastCases (by simp [floorMeasure, map_orbitPoint_topFloorMeasure]) fun a ↦
               ?_⟩
  -- Below floor ϱ, integrate a test function `Φ` in the flat chart `χ` of the quadric. A chart
  -- point is the value of `orbitPoint` at a point of the big cell, the inverse of `floorWeyl a t`
  -- times a Heisenberg element.
  refine ext_of_lintegral _ fun Φ hΦ ↦ ?_
  let V : Type := {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A
  let χ (t : A) (u : V) (β : skewAdjoint A) : 𝔰.BesselIndex → A :=
    inclMatrix A (floorIndexEnum a) *ᵥ flatChart (upperGram (T := T) (a + 1)) 0 ((t, u), β)
  set d : ℕ := 𝔰.k + 1 + 2 * (𝔰.ϱ - (a + 1)) with hd
  -- both integrals are iterated integrals over `t`, the higher floors and the skew elements
  have h_floor : ∫⁻ v, Φ v ∂(F.floorMeasure a.castSucc).map (orbitPoint a.castSucc) =
      ∫⁻ t : A, modulus t ^ d * ∫⁻ u : V, ∫⁻ β : skewAdjoint A,
        Φ (orbitPoint a.castSucc ((floorWeyl a t : T.G)⁻¹ * heisenbergElem a (u, β)))
          ∂P.skewMeasure := by
    -- `fun_prop` has to unfold the measurable space that `volume` carries
    simp (disch := with_unfolding_all fun_prop) [floorMeasure, heisenbergMeasure, lintegral_map,
      mconv, lintegral_prod, lintegral_withDensity_eq_lintegral_mul, hd, V]
  have h_quadric : ∫⁻ v, Φ v ∂F.floorQuadricMeasure a.castSucc =
      ∫⁻ t : A, ∫⁻ u : V, ∫⁻ β : skewAdjoint A, Φ (χ t u β) ∂P.skewMeasure := by
    rw [floorQuadricMeasure_castSucc_eq_map]
    simp (disch := with_unfolding_all fun_prop)
      [lintegral_map, lintegral_prod, volume_eq_prod, χ, V]
  rw [h_floor, h_quadric]
  refine lintegral_congr_of_ae_imp ae_isUnit ?_
  rintro _ ⟨t, rfl⟩
  calc _ = modulus t.val ^ d *
        ∫⁻ u : V, ∫⁻ β : skewAdjoint A, Φ (χ t (t.val • u) β) ∂P.skewMeasure := by
        -- `orbitPoint` inverts, and the inverse of `heisenbergElem a (u, β)` has parameters
        -- `(-u, c - β)` with `c` independent of `β`; both substitutions keep the measure
        rw [← lintegral_neg_eq_self]
        refine congrArg _ (lintegral_congr fun u ↦ ?_)
        let v : 𝔰.BesselIndex → A := inclMatrix A (↑) *ᵥ (-u)
        let c : skewAdjoint A := skewPart (element * star v ⬝ᵥ T.splitGram *ᵥ v)
        have h_point (β : skewAdjoint A) :
            orbitPoint a.castSucc ((floorWeyl a t.val : T.G)⁻¹ * heisenbergElem a (-u, β)) =
              χ t (t.val • u) (c - β) := by
          refine .trans ?_ (inclMatrix_mulVec_flatChart_eq_heisenbergElem_mulVec a t u (c - β)).symm
          rw [mulVec_mulVec]
          simp [orbitPoint, heisenbergElem_inv, c, v]
        simp only [h_point]
        exact lintegral_sub_left_eq_self (fun β : skewAdjoint A ↦ Φ (χ t (t.val • u) β)) c
    _ = ∫⁻ u : V, ∫⁻ β : skewAdjoint A, Φ (χ t u β) ∂P.skewMeasure := by
      -- scaling the higher floors by `t` has modulus `modulus t` to the power of their dimension
      have h_scale : (volume : Measure V).map (t.val • ·) = (modulus t.val ^ d)⁻¹ • volume := by
        simpa [↓card_subtype_succ_le_floorOf_eq, smul_mulVec] using
          map_mulVec_volume _ (t.val • (1 : Matrix {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} _ A))
            (by simp [t.isUnit.pow])
      rw [eq_comm, lintegral_eq_mul_lintegral_map h_scale (by simp) (by simp),
        lintegral_map (by fun_prop) (by fun_prop)]

/-- For a floor `b : Fin 𝔰.n`, that is b ≤ ϱ, and s in G^(b) = `floorGroup b`, the map σ ↦ s σ⁻¹ f,
with f the frame vector of floor b, carries the floor measure `F.floorMeasure b` to the quadric
measure `F.floorQuadricMeasure b`. -/
lemma measurePreserving_mulVec_orbitPoint {s : T.G} {F : PlaceData ι T m} (b : Fin 𝔰.n)
    (hs : s ∈ floorGroup b) :
    MeasurePreserving (s *ᵥ orbitPoint b ·) (F.floorMeasure b) (F.floorQuadricMeasure b) := by
  -- `s` preserves `floorVolume b` and the form, hence the disintegration along the form.
  let M : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := s
  have h_incl : MeasurePreserving
      (fun v : {i : 𝔰.BesselIndex // b ≤ floorOf i} → A ↦ inclMatrix A Subtype.val *ᵥ v)
      volume (floorVolume b) :=
    (by fun_prop : Measurable _).measurePreserving volume
  -- extension by zero intertwines `M` with its block on the floors from `b` on
  have h_vol : MeasurePreserving (M *ᵥ ·) (floorVolume b) (floorVolume b) :=
    h_incl.of_semiconj (measurePreserving_floor_block_mulVec hs)
      (inclMatrix_mulVec_floor_block b.is_le hs) (by fun_prop)
  have h_form : Mᴴ * T.splitGram * M = T.splitGram := s.prop
  have h_inv : s⁻¹.val.val * M = 1 := s.val.inv_mul
  have h_image : IsDisintegration ((floorVolume b).map (M *ᵥ ·)) T.splitGram
      fun β : skewAdjoint A ↦ (F.floorQuadricMeasure b β).map (M *ᵥ ·) :=
    (F.isDisintegration_floorVolume b rfl).map h_form h_inv
  have h_same : IsDisintegration ((floorVolume b).map (M *ᵥ ·)) T.splitGram
      fun β : skewAdjoint A ↦ F.floorQuadricMeasure b β :=
    F.isDisintegration_floorVolume b h_vol.map_eq
  have h_quadric :
      MeasurePreserving (M *ᵥ ·) (F.floorQuadricMeasure b) (F.floorQuadricMeasure b) :=
    { measurable := h_vol.measurable, map_eq := h_image.unique h_same }
  exact h_quadric.comp (measurePreserving_orbitPoint b)

/-- The measure θ_l = `F.floorMeasure l` of floor l is concentrated on the group
G^(l) = `floorGroup l`: almost every `x` lies in `floorGroup l`. -/
lemma ae_floorMeasure_mem : ∀ᵐ x : T.G ∂F.floorMeasure l, x ∈ floorGroup l := by
  fun_cases floorMeasure
  · -- below floor ϱ, both factors are carried by G^(l)
    have h_heisenberg : ∀ᵐ x : T.G ∂heisenbergMeasure l, x ∈ floorGroup l :=
      ae_mem_floorUnipotent.mono fun x hx ↦ hx.1
    have h_weyl : ∀ᵐ x : T.G ∂weylLaw l, x ∈ floorGroup l := by
      simp [ae_map_iff measurable_floorWeyl.fun_inv.aemeasurable, measurableSet_floorGroup]
    exact ae_mem_mconv h_weyl h_heisenberg measurableSet_floorGroup
  -- floors ϱ and ϱ + 1 carry `F.topFloorMeasure` and `F.measureH`, the higher ones the Dirac
  -- measure at 1
  case case2 h_floor => simp [ae_topFloorMeasure_mem_floorGroup, h_floor]
  case case3 h_floor => simp [ae_measureH_mem_besselH, h_floor]
  case case4 => simp

/-- Congruence rule for integrals over floor `l`: since `F.floorMeasure l` is carried by the group
G^(l) = `floorGroup l`, the integrand may be changed outside G^(l). -/
@[congr]
lemma lintegral_floorMeasure_congr {μ : Measure T.G} (hμ : F.floorMeasure l = μ)
    (h_eq : ∀ σ ∈ floorGroup l, f σ = Φ σ) :
    lintegral (F.floorMeasure l) f = lintegral μ Φ := by
  rw [← hμ]
  exact lintegral_congr_of_ae_imp ae_floorMeasure_mem h_eq

/-- The measure of floor `𝔰.n = ϱ + 1` is the measure of H. -/
@[simp]
lemma floorMeasure_top : F.floorMeasure 𝔰.n = F.measureH := by simp [floorMeasure]

/-- The convolution θ_{ϱ+1} ∗ ⋯ ∗ θ_l of the floor measures from floor `l` on is the convolution
from floor `l + 1` on, convolved with θ_l = `F.floorMeasure l`. -/
lemma quotientMeasureFrom_eq_succ_mconv :
    F.quotientMeasureFrom l = F.quotientMeasureFrom (l + 1) ∗ₘ F.floorMeasure l := by
  obtain hl | hl : l < 𝔰.ϱ + 2 ∨ 𝔰.ϱ + 2 ≤ l := lt_or_ge l (𝔰.ϱ + 2)
  · rw [quotientMeasureFrom, show 𝔰.ϱ + 2 - l = 𝔰.ϱ + 2 - (l + 1) + 1 by lia, descConv]
  · -- all three measures are the Dirac measure at 1
    have h_dirac : F.floorMeasure l = dirac 1 := by grind [floorMeasure]
    rw [h_dirac, mconv_dirac_one, quotientMeasureFrom, quotientMeasureFrom,
      Nat.sub_eq_zero_of_le hl,
      Nat.sub_eq_zero_of_le (hl.trans l.le_succ), descConv, descConv]

/-- Let l < ϱ = `𝔰.ϱ`, the number of hyperbolic pairs, and let θ_a = `F.floorMeasure a`. Then
θ_{l+i} ∗ ⋯ ∗ θ_l equals `weylLaw l` ∗ (θ_{l+i} ∗ ⋯ ∗ θ_{l+1}) ∗ η_l. Here `weylLaw l` is carried by
the inverses of the elements `floorWeyl l c` that swap the lines of e_l and e*_l, and
η_l = `heisenbergMeasure l` is the Haar measure of the Heisenberg group attached to e_l. -/
lemma descConv_floorMeasure_succ {F : PlaceData ι T m} (h : l < 𝔰.ϱ) :
    descConv F.floorMeasure l (i + 1) =
      (weylLaw l ∗ₘ descConv F.floorMeasure (l + 1) i) ∗ₘ heisenbergMeasure l := by
  -- `weylLaw l` commutes with the higher floors, which are carried by `G^(l+1)`
  have h_comm :
      descConv F.floorMeasure (l + 1) i ∗ₘ weylLaw l =
        weylLaw l ∗ₘ descConv F.floorMeasure (l + 1) i := by
    refine mconv_comm_of_ae ((ae_descConv_mem ae_floorMeasure_mem).mono fun s hs ↦ ?_)
    have h_commute (c : A) : (floorWeyl l c : T.G)⁻¹ * s = s * (floorWeyl l c)⁻¹ :=
      (commute_weylOn (by lia) hs).inv_left.eq
    simp (disch := fun_prop) [dirac_mconv, mconv_dirac, Measure.map_map, comp_def, h_commute]
  rw [descConv, floorMeasure, ite_eq_left h, ← mconv_assoc, h_comm]

omit [TopologicalSpace A] [MeasureSpace A] [Place A] [IsHermitianUnit T.splitGram] in
/-- Let j < ϱ and let w_j(c) = `floorWeyl j c` be the Weyl element of floor j with unit parameter
c. The diagonal elements `weylRatio (j + 1) p q` and `weylRatio j p q`, with entries p_a / q_a at
the e_a, differ by a factor that takes w_j((p_j / q_j) c)⁻¹ to w_j(c)⁻¹. -/
lemma weylRatio_succ_mul_floorWeyl_inv (hj : j < 𝔰.ϱ) (p q : ℕ → Aˣ) (c : Aˣ) :
    weylRatio (j + 1) p q * (floorWeyl j ((p j / q j).val * c : A))⁻¹ =
      (weylRatio j p q * (floorWeyl j (c : A))⁻¹ : T.G) := by
  -- Compare the entries: both sides are a diagonal matrix times a monomial matrix. The `simp` call
  -- writes the entries as case distinctions on the floor and level of the two indices.
  ext a b
  simp [coe_weylRatio, floorWeyl, weylOn, division_def, Ring.mul_inverse_rev]
  grind [Units.inv_mul, =_ star_mul, oppositeIndex_involutive_and_floorOf_level]

/-- Let j ≤ ϱ = `𝔰.ϱ`, the number of hyperbolic pairs e_a, e*_a, and let `weylRatio j p q` be the
diagonal isometry that scales e_a by p_a / q_a for a < j. Left translation by it multiplies the
integral of a measurable Φ ≥ 0 for `F.quotientMeasureFrom 0`, the convolution of all the measures
`F.floorMeasure a`, by the product over a < j of |p_a / q_a| ^ (k + 2 (ϱ - a)). Here k = `𝔰.k` and
|·| is the `modulus` of the ring `A`, the factor by which a unit scales its volume. -/
lemma lintegral_weylRatio_mul {Φ : T.G → ℝ≥0∞} {F : PlaceData ι T m} {p q : ℕ → Aˣ} (hj : j ≤ 𝔰.ϱ)
    (hΦ : Measurable Φ) :
    ∫⁻ x : T.G, Φ (weylRatio j p q * x) ∂F.quotientMeasureFrom 0 =
      (∏ a ∈ Finset.range j, modulus (p a / q a).val ^ (𝔰.k + 2 * (𝔰.ϱ - a))) *
        ∫⁻ x : T.G, Φ x ∂F.quotientMeasureFrom 0 := by
  induction j with
  | zero => simp [weylRatio]
  | succ j ih =>
    -- split off the Weyl element of floor `j`; `μ` is the rest of the convolution
    let μ : Measure T.G :=
      descConv F.floorMeasure (j + 1) (𝔰.ϱ - j + 1) ∗ₘ heisenbergMeasure j ∗ₘ
        descConv F.floorMeasure 0 j
    have hμ : F.quotientMeasureFrom 0 = weylLaw j ∗ₘ μ := by
      rw [quotientMeasureFrom, show 𝔰.ϱ + 2 - 0 = j + (𝔰.ϱ - j + 1 + 1) by lia,
        descConv_add, zero_add, descConv_floorMeasure_succ hj, mconv_assoc, mconv_assoc]
    -- integrate first over the parameter `c` of that Weyl element
    have h_split (Ψ : T.G → ℝ≥0∞) (hΨ : Measurable Ψ) :
        ∫⁻ x : T.G, Ψ x ∂F.quotientMeasureFrom 0 =
          ∫⁻ c : A, P.modulus c ^ (𝔰.k + 1 + 2 * (𝔰.ϱ - (j + 1))) *
            ∫⁻ y : T.G, Ψ ((floorWeyl j c)⁻¹ * y) ∂μ := by
      rw [hμ, lintegral_mconv hΨ, lintegral_map (by fun_prop) (by fun_prop),
        lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
      simp only [Pi.mul_apply]
    -- rescaling the parameter of the Weyl element by `r` absorbs the new factor
    set r : Aˣ := p j / q j with hr
    have h_shift (c : Aˣ) :
        weylRatio (j + 1) p q * (floorWeyl j (r * c : A))⁻¹ =
          (weylRatio j p q * (floorWeyl j (c : A))⁻¹ : T.G) :=
      weylRatio_succ_mul_floorWeyl_inv hj p q c
    have h_exp : 𝔰.k + 2 * (𝔰.ϱ - j) = 𝔰.k + 1 + 2 * (𝔰.ϱ - (j + 1)) + 1 := by lia
    have hΦ_shift (n : ℕ) : Measurable fun x : T.G ↦ Φ (weylRatio n p q * x) := by fun_prop
    -- by induction it suffices to compare the translations by the elements of length `j + 1`, `j`
    rw [Finset.prod_range_succ_comm, ← hr, mul_assoc, ← ih (by lia), h_split _ (hΦ_shift (j + 1)),
      h_split _ (hΦ_shift j)]
    -- substitute `r * c` for `c` on the left, which costs the factor `modulus r`
    rw [lintegral_eq_mul_lintegral_map (map_mul_volume r) (modulus_ne_zero r) (modulus_ne_top r),
      lintegral_map (by fun_prop) (by fun_prop), ← lintegral_const_mul _ (by fun_prop),
      ← lintegral_const_mul _ (by fun_prop)]
    -- almost every parameter is a unit, where `h_shift` applies
    refine lintegral_congr_ae (ae_isUnit.mono ?_)
    rintro _ ⟨c, rfl⟩
    simp [h_exp, h_shift, mul_pow, ← mul_assoc, pow_succ']

/-- Let S be a subgroup that contains G^(l) = `floorGroup l`, the isometries fixing the basis
vectors of floor below l, and let R^(l) = `partialUnitriangularGroup l` be the group of the
isometries unitriangular on the first l frame vectors. If f ≥ 0 is measurable and left invariant
under R^(l+1) ∩ S, its integral for the measure `F.floorMeasure l` on G^(l) does not change under
right translation by an element s of R^(l) ∩ S. -/
lemma lintegral_floorMeasure_mul_right {s : T.G} {S : Subgroup T.G} {f : T.G → ℝ≥0∞}
    {F : PlaceData ι T m} (hS : floorGroup l ≤ S)
    (hf_inv : (partialUnitriangularGroup (l + 1) ⊓ S).FixesLeft f)
    (hs : s ∈ partialUnitriangularGroup l ⊓ S) (hf : Measurable f := by fun_prop) :
    ∫⁻ x : T.G, f (x * s) ∂F.floorMeasure l = ∫⁻ x : T.G, f x ∂F.floorMeasure l := by
  obtain ⟨hs_unitri, hsS⟩ : s ∈ partialUnitriangularGroup l ∧ s ∈ S := Subgroup.mem_inf.mp hs
  obtain ⟨γ, hγ, ν, hν, rfl⟩ : ∃ γ ∈ floorGroup l, ∃ ν ∈ unipotentBelow l, s = γ * ν :=
    exists_floorGroup_mul_unipotentBelow hs_unitri
  -- The factor ν drops out: x γ ν = ((x γ) ν (x γ)⁻¹) x γ, and f is invariant under the conjugate.
  have h_drop (x : T.G) (hx : x ∈ floorGroup l) : f (x * (γ * ν)) = f (x * γ) := by
    have h_unitri : x * γ * ν * (x * γ)⁻¹ ∈ partialUnitriangularGroup (l + 1) :=
      unipotentBelow_le_partialUnitriangularGroup (conj_mem_unipotentBelow (mul_mem hx hγ) hν)
    have h_mem : x * γ * ν * (x * γ)⁻¹ ∈ S := by
      rw [mul_assoc x γ]
      exact mul_mem (mul_mem (hS hx) hsS) (inv_mem (hS (mul_mem hx hγ)))
    calc f (x * (γ * ν)) = f (x * γ * ν * (x * γ)⁻¹ * (x * γ)) := by
          rw [inv_mul_cancel_right, mul_assoc]
      _ = f (x * γ) := hf_inv _ ⟨h_unitri, h_mem⟩ (x * γ)
  rw [lintegral_floorMeasure_congr rfl h_drop]
  obtain h | rfl | h := lt_trichotomy l 𝔰.n
  · -- On G^(l), `f = f₀ ∘ orbitPoint b`; the points of `x` and of `x γ` differ by the action of
    -- `γ⁻¹`, and both maps carry the floor measure to the same quadric measure.
    let b : Fin 𝔰.n := ⟨l, h⟩
    obtain ⟨f₀, hf₀, hf_eq⟩ : ∃ f₀ : (𝔰.BesselIndex → A) → ℝ≥0∞,
        Measurable f₀ ∧ ∀ x ∈ floorGroup l, f x = f₀ (orbitPoint b x) :=
      exists_factor_orbitPoint b hf fun t ⟨ht_unitri, ht⟩ ↦ hf_inv t ⟨ht_unitri, hS ht⟩
    calc ∫⁻ x : T.G, f (x * γ) ∂F.floorMeasure l
        = ∫⁻ x : T.G, f₀ ((γ⁻¹ : T.G) *ᵥ orbitPoint b x) ∂F.floorMeasure l := by
          refine lintegral_floorMeasure_congr rfl fun x hx ↦ ?_
          rw [hf_eq _ (mul_mem hx hγ), orbitPoint, orbitPoint, mulVec_mulVec, _root_.mul_inv_rev,
            Subgroup.coe_mul, Units.val_mul]
      _ = ∫⁻ v : 𝔰.BesselIndex → A, f₀ v ∂F.floorQuadricMeasure b :=
          (measurePreserving_mulVec_orbitPoint b (inv_mem hγ)).lintegral_comp hf₀
      _ = ∫⁻ x : T.G, f₀ (orbitPoint b x) ∂F.floorMeasure l :=
          ((measurePreserving_orbitPoint b).lintegral_comp hf₀).symm
      _ = ∫⁻ x : T.G, f x ∂F.floorMeasure l := (lintegral_floorMeasure_congr rfl hf_eq).symm
  · -- on the last floor G^(l) is H, under which `F.measureH` is right invariant
    rw [floorMeasure_top, ← lintegral_mconv_dirac, F.measureH_mconv_dirac (by simpa using hγ)]
  · -- above the last floor the group G^(l) is trivial
    have hγ_one : γ = 1 := by simpa [floorGroup_eq_bot h] using hγ
    simp [hγ_one]

/-- The convolution `F.partialGroupMeasure l i` of the Heisenberg and floor measures of the `i`
floors from `l` on is carried by G^(l) = `floorGroup l`, the isometries fixing the basis vectors of
floor below `l`. -/
lemma ae_partialGroupMeasure_mem {F : PlaceData ι T m} :
    ∀ᵐ x : T.G ∂F.partialGroupMeasure l i, x ∈ floorGroup l := by
  have h_heisenberg {a : ℕ} : ∀ᵐ x : T.G ∂heisenbergMeasure a, x ∈ floorGroup a :=
    ae_mem_floorUnipotent.mono fun x hx ↦ hx.1
  exact ae_descConv_mem (ae_mem_mconv h_heisenberg ae_floorMeasure_mem)

/-- Let η_a = `heisenbergMeasure a` and θ_a = `F.floorMeasure a`. If l + i = ϱ + 2, the convolution
(η_{ϱ+1}∗θ_{ϱ+1}) ∗ ⋯ ∗ (η_l∗θ_l) of i factors is invariant under right translation by every s in
G^(l) = `floorGroup l`. -/
lemma partialGroupMeasure_mconv_dirac {s : T.G} {F : PlaceData ι T m} (h : l + i = 𝔰.ϱ + 2)
    (hs : s ∈ floorGroup l) :
    F.partialGroupMeasure l i ∗ₘ dirac s = F.partialGroupMeasure l i := by
  induction i generalizing l s with
  | zero =>
    have hl : 𝔰.ϱ + 2 ≤ l := by lia
    have hs_one : s = 1 := by simpa [floorGroup_eq_bot hl] using hs
    rw [hs_one, mconv_dirac_one]
  | succ i ih =>
    -- Write the measure as `ρ ∗ₘ F.floorMeasure l` and apply `lintegral_floorMeasure_mul_right` to
    -- the `ρ`-average of a test function.
    let ρ : Measure T.G := F.partialGroupMeasure (l + 1) i ∗ₘ heisenbergMeasure l
    have h_split : F.partialGroupMeasure l (i + 1) = ρ ∗ₘ F.floorMeasure l := by
      rw [partialGroupMeasure, descConv, mconv_assoc]
    -- An element `t` of `R^(l+1) ∩ G^(l)` is `u * n` with `u` in `G^(l+1)`, absorbed by induction,
    -- and `n` in the Heisenberg group of floor `l`, absorbed by `heisenbergMeasure l`.
    have hρ_right (t : T.G) (ht : t ∈ partialUnitriangularGroup (l + 1) ⊓ floorGroup l) :
        ρ ∗ₘ dirac t = ρ := by
      obtain ⟨u, hu, n, hn, rfl⟩ :
          ∃ u ∈ floorGroup (l + 1), ∃ n ∈ floorUnipotent l, t = u * n :=
        exists_floorGroup_mul_floorUnipotent ht
      obtain ⟨hn_right, -⟩ := heisenbergMeasure_mconv_dirac hn
      have hu_right : F.partialGroupMeasure (l + 1) i ∗ₘ dirac u = F.partialGroupMeasure (l + 1)
        i :=
        ih (by lia) hu
      calc ρ ∗ₘ dirac (u * n)
          = F.partialGroupMeasure (l + 1) i ∗ₘ (heisenbergMeasure l ∗ₘ dirac u) ∗ₘ dirac n := by
            simp only [ρ, ← dirac_mconv_dirac, mconv_assoc]
        _ = (F.partialGroupMeasure (l + 1) i ∗ₘ dirac u) ∗ₘ (heisenbergMeasure l ∗ₘ dirac n) := by
            simp only [← dirac_mconv_heisenbergMeasure_comm hu, mconv_assoc]
        _ = ρ := by rw [hu_right, hn_right]
    refine ext_of_lintegral _ fun f hf ↦ ?_
    let avg (y : T.G) : ℝ≥0∞ := ∫⁻ x : T.G, f (x * y) ∂ρ
    have h_inv : (partialUnitriangularGroup (l + 1) ⊓ floorGroup l).FixesLeft avg := by
      intro t ht g
      simp only [avg, ← lintegral_mconv_dirac, ← dirac_mconv_dirac, ← mconv_assoc, hρ_right t ht]
    calc ∫⁻ x : T.G, f x ∂(F.partialGroupMeasure l (i + 1) ∗ₘ dirac s)
        = ∫⁻ y : T.G, avg (y * s) ∂F.floorMeasure l := by
          rw [lintegral_mconv_dirac, h_split, lintegral_mconv_symm (by fun_prop)]
          simp only [avg, mul_assoc]
      _ = ∫⁻ y : T.G, avg y ∂F.floorMeasure l :=
          lintegral_floorMeasure_mul_right le_rfl h_inv
            ⟨mem_partialUnitriangularGroup_of_mem_floorGroup hs, hs⟩
      _ = ∫⁻ x : T.G, f x ∂F.partialGroupMeasure l (i + 1) := by
        rw [h_split, lintegral_mconv_symm hf]

/-- The group measure, the convolution over all floors, is right invariant. -/
instance isMulRightInvariant_groupMeasure : F.groupMeasure.IsMulRightInvariant where
  map_mul_right_eq_self g := by
    -- G^(0) is the whole group
    have hg : g ∈ floorGroup 0 := by simp
    rw [← mconv_dirac, groupMeasure, partialGroupMeasure_mconv_dirac (zero_add (𝔰.ϱ + 2)) hg]

/-- Let η_a = `heisenbergMeasure a` and θ_a = `F.floorMeasure a`. The measure
`F.partialGroupMeasure 0 j` = (η_{j−1}∗θ_{j−1}) ∗ ⋯ ∗ (η₀∗θ₀) equals the ascending convolution η₀ ∗
⋯ ∗ η_{j−1} convolved with the descending convolution θ_{j−1} ∗ ⋯ ∗ θ₀. -/
lemma partialGroupMeasure_zero_eq {F : PlaceData ι T m} :
    F.partialGroupMeasure 0 j = ascConv heisenbergMeasure j ∗ₘ descConv F.floorMeasure 0 j := by
  induction j with
  | zero => simp [descConv, ascConv]
  | succ j ih =>
    -- `F.floorMeasure j` is carried by `floorGroup j`, so it commutes with the lower
    -- `heisenbergMeasure`.
    have h_comm :
        F.floorMeasure j ∗ₘ ascConv heisenbergMeasure j =
          ascConv heisenbergMeasure j ∗ₘ F.floorMeasure j :=
      mconv_comm_of_ae (F.ae_floorMeasure_mem.mono ascConv_heisenbergMeasure_dirac_comm)
    calc F.partialGroupMeasure 0 (j + 1)
        = (heisenbergMeasure j ∗ₘ F.floorMeasure j) ∗ₘ F.partialGroupMeasure 0 j := by
          simp only [partialGroupMeasure, descConv_succ]
      _ = heisenbergMeasure j ∗ₘ ((F.floorMeasure j ∗ₘ ascConv heisenbergMeasure j) ∗ₘ
            descConv F.floorMeasure 0 j) := by
          simp only [ih, mconv_assoc]
      _ = ascConv heisenbergMeasure (j + 1) ∗ₘ descConv F.floorMeasure 0 (j + 1) := by
          simp only [h_comm, descConv_succ, ascConv_heisenbergMeasure_succ, mconv_assoc]

/-- The measure θ_l = `F.floorMeasure l` of every floor of the place datum `F` is non-zero. -/
lemma floorMeasure_ne_zero {F : PlaceData ι T m} (l : ℕ) : F.floorMeasure l ≠ 0 := by
  obtain hl | rfl | hl : l < 𝔰.n ∨ l = 𝔰.n ∨ 𝔰.n < l := lt_trichotomy l 𝔰.n
  · -- the measure maps onto a non-zero quadric measure
    have h_map : (F.floorMeasure l).map (orbitPoint ⟨l, hl⟩) = F.floorQuadricMeasure ⟨l, hl⟩ :=
      (measurePreserving_orbitPoint ⟨l, hl⟩).map_eq
    have h_quadric : F.floorQuadricMeasure ⟨l, hl⟩ ≠ 0 := by
      simp (disch := fun_prop) [NeZero.ne]
    intro h_zero
    rw [h_zero, Measure.map_zero] at h_map
    exact h_quadric h_map.symm
  · rw [floorMeasure_top]
    exact NeZero.ne F.measureH
  · have h_dirac : F.floorMeasure l = dirac 1 := by grind [floorMeasure]
    rw [h_dirac]
    exact dirac_ne_zero

/-- The measure `F.partialGroupMeasure l i` of the place data `F` is non-zero. It is the convolution
of the measures `heisenbergMeasure a` and `F.floorMeasure a` over the `i` floors l ≤ a < l + i.
Floor a < ϱ is the hyperbolic pair e_a, e*_a, floor ϱ is z, and floor ϱ + 1 holds the other middle
vectors. -/
lemma partialGroupMeasure_ne_zero {F : PlaceData ι T m} : F.partialGroupMeasure l i ≠ 0 := by
  have h_heis (a : ℕ) : (heisenbergMeasure a : Measure T.G) ≠ 0 := by
    obtain ha | ha : a < 𝔰.ϱ ∨ 𝔰.ϱ ≤ a := lt_or_ge a 𝔰.ϱ
    · -- it is a factor of `F.floorMeasure a`
      intro h_zero
      apply F.floorMeasure_ne_zero a
      rw [floorMeasure, ite_eq_left ha, h_zero, mconv_zero]
    · rw [heisenbergMeasure_eq_dirac_one ha]
      exact dirac_ne_zero
  -- the total mass of a convolution is the product of the total masses
  have h_univ (μ μ' : Measure T.G) [SFinite μ] [SFinite μ'] :
      (μ ∗ₘ μ') Set.univ = μ Set.univ * μ' Set.univ := by
    simp [mconv_apply_eq_lintegral .univ]
  rw [← measure_univ_ne_zero]
  induction i generalizing l with
  | zero => simp [descConv]
  | succ i ih =>
    have h_mass : F.partialGroupMeasure l (i + 1) Set.univ = F.partialGroupMeasure (l + 1) i
      Set.univ *
        (heisenbergMeasure (T := T) l Set.univ * F.floorMeasure l Set.univ) := by
      rw [partialGroupMeasure, descConv, h_univ, h_univ]
    rw [h_mass]
    refine mul_ne_zero ih ?_
    simp [h_heis, floorMeasure_ne_zero]

/-- Let the measure `F.groupMeasure` on the unitary group, the convolution over all floors, be a
Haar measure and equal `ρ ∗ ν`, with `ρ` carried by the subgroup `S`, right invariant under `S` and
commuting with the unit mass at `s`. Then left translation by `s` does not change the `ν`-integral
of a measurable `Φ ≥ 0` that is invariant under left translation by `S` (`S.FixesLeft Φ`). -/
lemma lintegral_mul_left_eq_of_factor {ν ρ : Measure T.G} [SFinite ν] [SFinite ρ] {s : T.G}
    {S : Subgroup T.G} {Φ : T.G → ℝ≥0∞} {F : PlaceData ι T m} [F.groupMeasure.IsHaarMeasure]
    (h_factor : F.groupMeasure = ρ ∗ₘ ν) (hρ_mem : ∀ᵐ y : T.G ∂ρ, y ∈ S)
    (hρ_right : ∀ t ∈ S, ρ ∗ₘ dirac t = ρ) (hs : dirac s ∗ₘ ρ = ρ ∗ₘ dirac s) (hΦ : Measurable Φ)
    (hΦ_inv : S.FixesLeft Φ) :
    ∫⁻ g : T.G, Φ (s * g) ∂ν = lintegral ν Φ := by
  -- Take `f > 0` integrable for `F.groupMeasure`. For any `μ` with `F.groupMeasure = ρ ∗ₘ μ`, the
  -- integral of `Φ` for `μ` is the integral for `F.groupMeasure` of `Φ * f` divided by the
  -- `ρ`-average of `f`, an expression that does not mention `μ`.
  obtain ⟨f, hf_pos, hf, hf_int⟩ : ∃ f : T.G → NNReal,
      (∀ x : T.G, 0 < f x) ∧ Measurable f ∧ ∫⁻ x : T.G, f x ∂F.groupMeasure < ∞ :=
    exists_pos_lintegral_lt_of_sigmaFinite F.groupMeasure top_ne_zero
  let avg (g : T.G) : ℝ≥0∞ := ∫⁻ y : T.G, f (y * g) ∂ρ
  have h_avg (y : T.G) (hy : y ∈ S) (g : T.G) : avg (y * g) = avg g :=
    calc ∫⁻ x : T.G, f (x * (y * g)) ∂ρ
        = ∫⁻ x : T.G, f (x * g) ∂(ρ ∗ₘ dirac y) := by
          rw [lintegral_mconv_dirac]
          simp only [mul_assoc]
      _ = avg g := by rw [hρ_right y hy]
  have hρ : ρ ≠ 0 := by
    rintro rfl
    exact F.partialGroupMeasure_ne_zero (h_factor.trans (zero_mconv ν))
  have h_avg_ne (g : T.G) : avg g ≠ 0 := by
    have hf_ne (x : T.G) : f x ≠ 0 := (hf_pos x).ne'
    simpa (disch := fun_prop) [avg, EventuallyEq, hf_ne] using hρ
  have h_formula (μ : Measure T.G) [SFinite μ] (hμ : F.groupMeasure = ρ ∗ₘ μ) :
      ∫⁻ x : T.G, Φ x / avg x * f x ∂F.groupMeasure = lintegral μ Φ := by
    rw [hμ, lintegral_mconv_symm (by fun_prop)] at hf_int ⊢
    have h_avg_lt : ∀ᵐ g : T.G ∂μ, avg g < ∞ := ae_lt_top (by fun_prop) hf_int.ne
    refine lintegral_congr_ae (h_avg_lt.mono fun g hg ↦ ?_)
    calc ∫⁻ y : T.G, Φ (y * g) / avg (y * g) * f (y * g) ∂ρ
        = ∫⁻ y : T.G, Φ g / avg g * f (y * g) ∂ρ :=
          lintegral_congr_ae (hρ_mem.mono fun y hy ↦ by simp only [hΦ_inv y hy g, h_avg y hy])
      _ = Φ g / avg g * avg g := lintegral_const_mul _ (by fun_prop)
      _ = Φ g := ENNReal.div_mul_cancel (h_avg_ne g) hg.ne
  -- the translate of `ν` by `s` is such a measure too, as `F.groupMeasure` is left invariant
  have h_translate : F.groupMeasure = ρ ∗ₘ (dirac s ∗ₘ ν) := by
    rw [← mconv_assoc, ← hs, mconv_assoc, ← h_factor, dirac_mconv, map_mul_left_eq_self]
  rw [← lintegral_dirac_mconv, ← h_formula _ h_translate, h_formula ν h_factor]

/-- Let `F.groupMeasure`, the convolution of the measures `heisenbergMeasure a` and
`F.floorMeasure a` over all ϱ + 2 floors a (ϱ = `𝔰.ϱ`), be a Haar measure. Let j ≤ ϱ + 2 and let `p`
be a sequence of units. Let w be the inverse of the Weyl element `weylElem j p`, which sends e_a to
p_a e*_a and e*_a to e_a / p̄_a for a < j and fixes the other basis vectors. If Φ ≥ 0 is measurable
and left invariant under G^(j) = `floorGroup j`, the isometries fixing the basis vectors of floor
below j, then Φ(w g) and Φ(g) have the same integral for the convolution `F.partialGroupMeasure 0 j`
over the floors below j. -/
lemma lintegral_partialGroupMeasure_weylElem_inv_mul {Φ : T.G → ℝ≥0∞} {F : PlaceData ι T m}
    [F.groupMeasure.IsHaarMeasure] (p : ℕ → Aˣ) (hΦ : Measurable Φ)
    (hΦ_inv : (floorGroup j).FixesLeft Φ) (hj : j ≤ 𝔰.ϱ + 2 := by lia) :
    ∫⁻ g : T.G, Φ ((weylElem j p)⁻¹ * g) ∂F.partialGroupMeasure 0 j =
      ∫⁻ g : T.G, Φ g ∂F.partialGroupMeasure 0 j := by
  -- Apply `lintegral_mul_left_eq_of_factor` to the floors `j, …, ϱ + 1` of `F.groupMeasure`; they
  -- are carried by `floorGroup j`, which commutes with `weylElem j p`.
  obtain ⟨i, hij⟩ : ∃ i : ℕ, 𝔰.ϱ + 2 = j + i := Nat.exists_eq_add_of_le hj
  have hM : F.groupMeasure = F.partialGroupMeasure j i ∗ₘ F.partialGroupMeasure 0 j := by
    rw [groupMeasure, hij, partialGroupMeasure, descConv_add, zero_add]
  have h_comm : F.partialGroupMeasure j i ∗ₘ dirac (weylElem j p)⁻¹ =
      dirac (weylElem j p)⁻¹ ∗ₘ F.partialGroupMeasure j i := by
    refine mconv_comm_of_ae (ae_partialGroupMeasure_mem.mono fun s hs ↦ ?_)
    have h_commute : (weylElem j p : T.G)⁻¹ * s = s * (weylElem j p)⁻¹ :=
      (commute_weylElem hs).inv_left.eq
    rw [dirac_mconv_dirac, dirac_mconv_dirac, h_commute]
  have h_right (t : T.G) (ht : t ∈ floorGroup j) :
      F.partialGroupMeasure j i ∗ₘ dirac t = F.partialGroupMeasure j i :=
    partialGroupMeasure_mconv_dirac hij.symm ht
  exact lintegral_mul_left_eq_of_factor hM ae_partialGroupMeasure_mem h_right h_comm.symm hΦ hΦ_inv

end PlaceData

end LevelGauge

end New.Floors

end
