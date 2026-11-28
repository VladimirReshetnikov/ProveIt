import Lib.SiegelWeil.OneVector.StandardQuadrics
import New.Spanning.Frames.QuadricPlancherel
import New.Spanning.Unfolding.BesselLevelStructure

/-!
# Place data and gauges at a finite place from the lattice of integral vectors

The estimates on the tower of unitary groups are proved for an abstract place `A` (a
`New.Floors.Place`) with a place datum (`New.Floors.PlaceData`) and a gauge (`New.Floors.Gauge`).
This file supplies these data at a finite place `New.Floors.IntegralPlace`, whose ring of integers
is `integers`, from the lattice of integral vectors. A finite place in this sense may be a finite
set of finite places read as one ring.

* `New.Floors.IntegralPlace.IsLatticeData`, `New.Floors.IntegralPlace.exists_isLatticeData`: the
  lattice datum, and its existence.
* `New.Floors.IntegralPlace.IsLargeLatticeData`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.gauge`: such a datum with rank bounds, a character
  trivial on traces and a unimodular group, and its gauges.
* `New.Floors.IntegralPlace.IsLargeLatticeData.heisenbergMeasure_eq_floorModulus`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.ascConv_mconv_unitaryLevel_coset`: masses of the
  congruence subgroup `K(g)` and its cosets.
* `New.Floors.IntegralPlace.IsLargeLatticeData.groupMeasure_boxSet_le`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.le_partialGroupMeasure_boxSet`,
  `New.Floors.IntegralPlace.IsLargeLatticeData.isHaarMeasure_groupMeasure`: bounds for the mass of
  the group of integral isometries, and the fact that `F.groupMeasure` is a Haar measure.

The form `h` has Gram matrix `T.splitGram`: `ϱ` hyperbolic planes and a middle block `T`. The number
`ϱ` comes from the shape `𝔰`. `New.unitaryLevel integers g J` is the congruence subgroup `K(g)` of
the unitary group (integral elements congruent to `1` modulo `g`), `P.modulus u` is the factor by
which a unit `u` scales the volume, and `z` is the last vector of the frame e_0, …, e_(ϱ-1), z.

Notions from other files:
* `New.latticeMiddleGram`: The Gram matrix of X₀ ⊕ Az in the basis x_i (i ≠ k₀), v, z, where
  v = x_{k₀}/p̄ + z/N and N = p p̄.
* `New.idealZeta`: The ideal zeta sum ∑ [R : I]^(−s) over the ideals I of finite index in R, for a
  natural number s, with values in [0, ∞].
* `New.Floors.HyperbolicBasis`: A basis of the middle block made of a first hyperbolic pair, `m`
  more pairs and an orthonormal part indexed by `ι`.
* `New.Shape.Form.besselU`, `New.Shape.Form.besselH`: The block upper unitriangular isometries, and
  the isometries that fix all basis vectors outside X₀.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Fintype PlaceData FloorGroups Pointwise Place
  SemilocalField Finset

/-! ### The vector `x - (π π̄)⁻¹ t z` in the lattice basis -/

section TailVector

variable {A : Type} {𝔰 : Shape} [CommRing A] [StarRing A]

/-- The vector x − (ππ̄)⁻¹t z of X₀ ⊕ Az, for x in `𝔰.κ → A` and t in A, written in the lattice
basis `besselLatticeBasis 𝔰 π`. -/
def vectorOfLastEntry (π : Aˣ) (t : A) (x : 𝔰.κ → A) : 𝔰.BesselIndex → A :=
  (besselLatticeBasis 𝔰 π)⁻¹.val *ᵥ (0 ⊕ᵥ ((x ⊕ᵥ fun _ : Unit ↦ -(π * star π)⁻¹ * t) ⊕ᵥ 0))

variable {π : Aˣ} {N t : A} {x : 𝔰.κ → A}

/-- Let `π π̄ = N`, let `h` be the form with Gram matrix `J = (latticeMiddleGram 𝔰 N).splitGram`,
and let `e = vectorOfLastEntry π t x`. Then (a) `h(e, e) = x* x - t t̄ / (π π̄)`, and (b)
`h(z, e) = t`. -/
lemma form_vectorOfLastEntry (hN : π * star ↑π = N) :
    let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := (latticeMiddleGram 𝔰 N).splitGram
    let e : 𝔰.BesselIndex → A := vectorOfLastEntry π t x
    -- (a) the value h(e, e)
    star e ⬝ᵥ J *ᵥ e = star x ⬝ᵥ x - (π * star π)⁻¹.val * t * star t ∧
    -- (b) the pairing h(z, e)
    (J *ᵥ e) 𝔰.z = t := by
  intro J e
  -- in the standard basis `e` has coordinates `v`, and the middle block is `middleGram`
  let B : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := besselLatticeBasis 𝔰 π
  let s : A := (π * star π)⁻¹.val * t
  let v : 𝔰.BesselIndex → A := 0 ⊕ᵥ ((x ⊕ᵥ fun _ : Unit ↦ -s) ⊕ᵥ 0)
  have h_coord : B *ᵥ e = v := by simp [B, e, v, s, vectorOfLastEntry, mulVec_mulVec]
  have h_pair : J *ᵥ e = Bᴴ *ᵥ (𝔰.middleGram N).splitGram *ᵥ v := by
    rw [← h_coord, mulVec_mulVec, mulVec_mulVec, gram_besselLatticeBasis π N hN]
  have h_cancel : N * s = t := by
    rw [← hN, ← mul_assoc, ← Units.coe_star, ← Units.val_mul, Units.mul_inv, one_mul]
  constructor
  · calc star e ⬝ᵥ J *ᵥ e
      _ = star v ⬝ᵥ (𝔰.middleGram N).splitGram *ᵥ v := by
        rw [h_pair, ← star_mulVec_dotProduct, h_coord]
      _ = star x ⬝ᵥ x - star s * (N * s) := by
        simp [v, splitGram, middleGram, mulVec, dotProduct, Matrix.one_apply, sub_eq_add_neg]
      _ = star x ⬝ᵥ x - (π * star π)⁻¹.val * t * star t := by
        rw [h_cancel]
        simp [s, mul_comm, mul_left_comm]
  · rw [h_pair, ← h_cancel]
    simp [B, v, besselLatticeBasis, splitGram, middleGram, mulVec, dotProduct, Matrix.one_apply]

/-- The vector `vectorOfLastEntry π t x` depends continuously on the pair `(t, x)`. -/
@[fun_prop]
lemma continuous_vectorOfLastEntry [TopologicalSpace A] [MeasureSpace A] [P : Place A] :
    Continuous fun z : A × (𝔰.κ → A) ↦ vectorOfLastEntry π z.1 z.2 := by
  refine continuous_const.matrix_mulVec (continuous_pi ?_)
  rintro (i | (i | i) | i) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> fun_prop

end TailVector

/-! ### The lattice datum of integral vectors -/

variable {ι : Type} {𝔰 : Shape} [Fintype ι] [DecidableEq ι] {m : ℕ}
  {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A]
  {T : 𝔰.Form A} [IsHermitianUnit T.splitGram] {g : Aˣ} (F : PlaceData ι T m)

/-- The principal congruence subgroup K(g) of the place datum `F`: the integral isometries congruent
to 1 modulo the unit `g = F.levelUnit`. -/
abbrev PlaceData.congruenceSubgroup : Subgroup (U T.splitGram) :=
  unitaryLevel O F.levelUnit T.splitGram

variable (𝔰 g) in
/-- The pairs (ω₁, ω₂) of vectors with ω₁ integral and ω₂ ≡ ω₁ modulo g. -/
abbrev IntegralPlace.congruentPairs : Set ((𝔰.BesselIndex → A) × (𝔰.BesselIndex → A)) :=
  {ω : (𝔰.BesselIndex → A) × (𝔰.BesselIndex → A) |
    ω.1 ∈ intVectors P.integers 𝔰.BesselIndex ∧ g⁻¹.val • (ω.1 - ω.2) ∈ intVectors P.integers
      𝔰.BesselIndex}

/-- For a unit `g` of the finite place `A`, the set `P.congruentPairs 𝔰 g` of the pairs (ω₁, ω₂)
with ω₁ and g⁻¹ (ω₁ - ω₂) integral is open, contains 0 and has compact closure. -/
lemma IntegralPlace.isOpen_congruentPairs_and_isCompact_closure :
    IsOpen (P.congruentPairs 𝔰 g) ∧ 0 ∈ P.congruentPairs 𝔰 g ∧
      IsCompact (closure (P.congruentPairs 𝔰 g)) := by
  obtain ⟨h_open, h_compact, -⟩ := isOpen_isCompact_volume_intVectors (A := A) (ι := 𝔰.BesselIndex)
  refine ⟨.inter (h_open.preimage continuous_fst) (h_open.preimage (by fun_prop)), by simp, ?_⟩
  -- The set lies in the image of the pairs of integral vectors under (ω, δ) ↦ (ω, ω - g δ).
  have h_image : IsCompact ((fun ω : (𝔰.BesselIndex → A) × (𝔰.BesselIndex → A) ↦
      (ω.1, ω.1 - g.val • ω.2)) ''
        (intVectors P.integers 𝔰.BesselIndex ×ˢ intVectors P.integers 𝔰.BesselIndex)) :=
    (h_compact.prod h_compact).image (by fun_prop)
  exact h_image.closure_of_subset fun ω hω ↦ ⟨(ω.1, g⁻¹.val • (ω.1 - ω.2)), hω, by simp [smul_smul]⟩

/-- The place datum `F` at a finite place is the one given by the lattice of integral vectors. Its
data are integral (`integral_data`). Its box is the group `K` of integral isometries, and its close
pairs are the pairs of integral vectors congruent modulo the level. Its measures are normalised or
bounded below on `K` (`volume_le_and_boxSet_closePairs_positions_eq`). An isotropic vector is dual
to the last frame vector (`exists_isotropic`). -/
structure IntegralPlace.IsLatticeData : Prop where
  /-- The Gram matrix is hermitian and invertible over `integers`, the basis `F.basisMatrix` is
  integral, and the unit `F.levelUnit` is integral and fixed by the involution. -/
  integral_data :
      IsUnimodular integers T.splitGram ∧ IsIntMatrix integers F.basisMatrix ∧ F.levelUnit.1 ∈
        integers ∧
        star F.levelUnit.1 = F.levelUnit
  /-- The box `F.boxSet` is the group of integral isometries. Its `F.topFloorMeasure`-measure is at
  least the volume of the units of `integers`, and its `F.measureH`-measure is `1`. The close pairs
  are the pairs of integral vectors congruent modulo `F.levelUnit`. The positions `F.positions` are
  the `y⁻¹ * u * y
  * k`, with `u` in `T.besselU` and `k` in `F.congruenceSubgroup`. -/
  volume_le_and_boxSet_closePairs_positions_eq :
      volume P.intUnits ≤ F.topFloorMeasure F.boxSet ∧
      F.boxSet = unitaryLevel integers 1 T.splitGram ∧
      F.measureH F.boxSet = 1 ∧
      F.closePairs = P.congruentPairs 𝔰 F.levelUnit ∧
      F.positions = {y⁻¹ * u * y | (y : T.G) (u ∈ T.besselU)} * F.congruenceSubgroup
  /-- There is a vector `u` such that pairing with `u` reads the coordinate at the last frame vector
  z, and this coordinate of `u` is zero; so `u` is isotropic with h(u, z) = 1. -/
  exists_isotropic : ∃ u : 𝔰.BesselIndex → A,
    star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1 ∧ u (𝔰.besselFrame 𝔰.top) = 0

/-- A lattice datum with `m + 1` further hyperbolic pairs is large if its ranks satisfy the bounds
of `zeta_le_and_le_card`, the character of the place is trivial on traces, and the unitary group is
unimodular. -/
class IntegralPlace.IsLargeLatticeData (F : PlaceData ι T (m + 1)) :
  Prop extends P.IsLatticeData F where
  /-- The ideal zeta sum of `P.integers` at `m` has `𝔰.n`-th power at most `1 + 2⁻¹ ^ 𝔰.n`, the
  number `m` is less than `9 * 𝔰.n`, and the orthonormal part of the basis has at least `53 * 𝔰.n`
  vectors. -/
  zeta_le_and_le_card :
      idealZeta P.integers m ^ 𝔰.n ≤ ENNReal.ofReal (1 + 2⁻¹ ^ 𝔰.n) ∧
      m < 9 * 𝔰.n ∧
      53 * 𝔰.n ≤ Fintype.card ι
  /-- The character of the place is trivial on traces. -/
  psi_add_star (x : A) : P.ψ (x + star x) = 1
  /-- The unitary group is unimodular: some left Haar measure is right invariant. -/
  unimodular : ∃ ν : Measure T.G, ν.IsHaarMeasure ∧ ν.IsMulRightInvariant

omit [IsHermitianUnit T.splitGram] in
/-- Let `T.G` be the unitary group of the form with middle block `T` over the finite place `A`, and
K = `unitaryLevel integers 1 T.splitGram` its subgroup of isometries over the ring of integers.
Let H = `T.besselH` be the fixer of the basis vectors outside `𝔰.κ`, and 𝖴 = `T.besselU` the group
of block upper unitriangular isometries. There is an s-finite measure on `T.G`, carried by H and
invariant under right translation by H, that gives K mass `1` and, for every `y`, gives the set
𝖴 K y⁻¹ mass at most `1`. -/
lemma IntegralPlace.exists_right_invariant_measure_besselH :
    ∃ η : Measure T.G,
      SFinite η ∧
      η (unitaryLevel integers 1 T.splitGram) = 1 ∧
      (∀ᵐ x : T.G ∂η, x ∈ T.besselH) ∧
      (∀ s ∈ T.besselH, η ∗ₘ dirac s = η) ∧
      ∀ y : T.G, η {h : T.G | ∃ u ∈ T.besselU, u * (h * y) ∈ unitaryLevel integers 1 T.splitGram} ≤
        1 := by
  -- `ν` is the right Haar measure on the closed subgroup `H` with ν (H ∩ K) = 1, and `η` its
  -- image in the whole group
  let K : Subgroup (U T.splitGram) := unitaryLevel integers 1 T.splitGram
  let H : Subgroup T.G := T.besselH
  have h_closed : IsClosed (H : Set T.G) := isClosed_of_entries_eq_one mem_floorGroup
  have h_emb : MeasurableEmbedding (Subtype.val : H → T.G) :=
    .subtype_coe h_closed.measurableSet
  have h_open : IsOpen (K : Set T.G)⁻¹ := IsOpen.inv unitaryLevel_open_compact.1
  let K₀ : TopologicalSpace.PositiveCompacts H :=
    ⟨⟨Subtype.val ⁻¹' (K : Set T.G)⁻¹, unitaryLevel_open_compact.2.inv.preimage_val h_closed⟩,
      1, by rw [h_open.preimage_val.interior_eq]; simp⟩
  let ν : Measure H := (haarMeasure K₀).inv
  let η : Measure T.G := ν.map Subtype.val
  have η_apply (S : Set T.G) : η S = ν (Subtype.val ⁻¹' S) := h_emb.map_apply ν S
  have η_box : η K = 1 :=
    calc η K = haarMeasure K₀ (Subtype.val ⁻¹' (K : Set T.G))⁻¹ := by rw [η_apply, inv_apply]
      _ = 1 := haarMeasure_self
  have η_right (s : T.G) (hs : s ∈ H) : η ∗ₘ dirac s = η := by
    have h_pres : MeasurePreserving (· * s) η η :=
      (h_emb.measurable.measurePreserving ν).of_semiconj (measurePreserving_mul_right ν ⟨s, hs⟩)
        (fun _ ↦ rfl) (by fun_prop)
    rw [mconv_dirac, h_pres.map_eq]
  -- the `h` in H with `h y ∈ besselU · K` lie in one right coset of H ∩ K
  have η_le (y : T.G) : η {h : T.G | ∃ u ∈ T.besselU, u * (h * y) ∈ K} ≤ 1 := by
    rw [← η_box, η_apply, η_apply]
    exact measure_le_of_div_mem fun h ⟨u, hu, huh⟩ ↦ ⟨h, fun k ⟨w, hw, hwk⟩ ↦
      div_mem_unitaryLevel_of_besselU_mul h.prop k.prop hu hw huh hwk⟩
  exact ⟨η, inferInstance, η_box, h_emb.ae_map_iff.mpr (by simp), η_right, η_le⟩

/-- Let `N` in `P.integers` be self-conjugate and let the rank `𝔰.k` of X₀ be `|ι| + 2 m + 1`. Then
the middle block `latticeMiddleGram 𝔰 N` has an integral hyperbolic basis in which the coordinate
at z (the index `inr ()`) of a vector is its coefficient at the second vector `inl 1` of the first
pair. -/
lemma IntegralPlace.exists_isIntMatrix_hyperbolicBasis {N : A} (hN : N ∈ P.integers)
    (hN_star : star N = N) (hm : 𝔰.k = Fintype.card ι + 2 * m + 1) :
    ∃ B : HyperbolicBasis ι (latticeMiddleGram 𝔰 N) m,
      IsIntMatrix P.integers B.basisMatrix ∧ B.basisMatrix (inr ()) = Pi.single (inl 1) 1 := by
  -- `E` makes the plane of `𝔰.k₀` and z hyperbolic, turns `2 * m` orthonormal vectors into `m`
  -- hyperbolic pairs by means of `c` with `star c * c = -1`, and keeps the others.
  obtain ⟨c, hc, hc_norm⟩ : ∃ c ∈ P.integers, star c * c = -1 := P.isAdelic.exists_norm_neg_one
  have f : SplitIndex m ι ≃ {i : 𝔰.κ // 𝔰.k₀ ≠ i} := equivOfCardEq (by simp +arith [hm])
  let C : Matrix (SplitIndex m ι) (SplitIndex m ι) A :=
    fromBlocks 1 (fromCols 0 (P.element • 1)) (fromRows 0 (c • 1))
      (fromBlocks 1 0 0 ((-star P.element * c) • 1))
  let E : Matrix 𝔰.MiddleIndex (Fin 2 ⊕ SplitIndex m ι) A :=
    inclMatrix A (![inl 𝔰.k₀, inr ()] ⊕ᵥ fun i ↦ inl (f i)) *
      fromBlocks !![-1, -N * P.element; 0, 1] 0 0 C
  have E_int : IsIntMatrix P.integers E :=
    .mul (by simp [IsIntMatrix, inclMatrix, Matrix.one_apply, ite_mem]) (by
      simp [C, hc, hN, IsIntMatrix, data_normalised, mul_mem, Matrix.one_apply, ite_mem,
        IsStarStable.star_mem])
  have E_form : Eᴴ * latticeMiddleGram 𝔰 N * E = planeSumGram (hyperbolicGram (Fin m) 1) := by
    have h_ne (i : SplitIndex m ι) : (f i : 𝔰.κ) ≠ 𝔰.k₀ := (f i).prop.symm
    have h_trace : P.element + star P.element = 1 := P.element_add_star
    rw [gram_mul, gram_inclMatrix]
    -- each entry reduces to `hc_norm`, `h_trace` or `hN_star`
    simp [← Matrix.ext_iff, Matrix.mul_apply, C, latticeMiddleGram, diagonal, h_ne,
      Subtype.val_inj, fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      conjTranspose_fromCols_eq_fromRows_conjTranspose, mul_assoc, mul_add, mul_sum,
      sum_add_distrib, Matrix.one_apply]
    grind
  obtain ⟨V, hV, hV_eq⟩ : ∃ V ∈ intGL 𝔰.MiddleIndex P.integers, V.val = latticeMiddleGram 𝔰 N :=
    (isUnimodular_latticeMiddleGram 𝔰 ⟨hN, hN_star⟩).2
  have h_det : P.modulus (latticeMiddleGram 𝔰 N).det = 1 := by rw [← hV_eq, modulus_det_eq_one hV]
  refine ⟨⟨E, E_form, by lia, h_det⟩, E_int, ?_⟩
  simp [E, funext_iff, Matrix.mul_apply, inclMatrix, Matrix.one_apply]

omit [IsHermitianUnit T.splitGram] in
/-- If a hyperbolic basis of the middle block is integral, so is the basis of each floor. -/
lemma IntegralPlace.isIntMatrix_floorBasis {B : HyperbolicBasis ι T m}
    (hB : IsIntMatrix P.integers B.basisMatrix) (b : Fin 𝔰.n) :
      IsIntMatrix P.integers (B.floorBasis b) := by
  refine .mul (.mul ?_ ?_) ?_
  · simp [IsIntMatrix, inclMatrix, Matrix.one_apply, ite_mem]
  · simp [IsIntMatrix, hB _, diagonal, ite_mem]
  · simp [IsIntMatrix, inclMatrix, Matrix.one_apply, ite_mem]

omit [IsHermitianUnit T.splitGram] in
/-- A combination of the columns of `B.floorBasis b`, the basis of the space of the floor `b`,
vanishes at every basis index whose floor (`floorOf`) is below `b`. -/
lemma HyperbolicBasis.floorBasis_mulVec_eq_zero (B : HyperbolicBasis ι T m) {b : Fin 𝔰.n}
    (v : Fin 2 ⊕ FloorPairs b m ⊕ ι ⊕ FloorPairs b m → A) {i : 𝔰.BesselIndex}
    (hi : floorOf i < b) : (B.floorBasis b *ᵥ v) i = 0 := by
  have hb : (b : ℕ) < 𝔰.ϱ + 1 := b.is_lt
  -- the columns of `floorBasis b` involve only basis indices of floor at least `b`
  simp only [floorBasis, ← mulVec_mulVec]
  refine sum_eq_zero fun j _ ↦ mul_eq_zero_of_left (one_apply_ne ?_) _
  rintro rfl
  rcases j with (j | j) | ⟨j, hj⟩ | ⟨j, hj⟩
  · -- an index of X₀ has floor `ϱ + 1`
    exact absurd (hi.trans hb) (lt_irrefl (𝔰.ϱ + 1))
  · -- the index of z has floor `ϱ`
    exact absurd hb (Nat.not_lt.2 hi)
  · exact absurd hi (Nat.not_lt.2 hj)
  · exact absurd hi (Nat.not_lt.2 hj)

omit [DecidableEq ι] in
/-- An integral form `J` takes values in `P.integers` on integral vectors. -/
lemma IntegralPlace.star_dotProduct_mulVec_mem_integers {J : Matrix ι ι A}
    (hJ : IsIntMatrix P.integers J) {v w : ι → A} (hv : v ∈ intVectors P.integers ι)
    (hw : w ∈ intVectors P.integers ι) : star v ⬝ᵥ J *ᵥ w ∈ P.integers :=
  sum_mem fun i _ ↦ mul_mem (isAdelic.toIsStarStable.star_mem (hv i)) (hJ.mulVec hw i)

omit [DecidableEq ι] in
/-- For an integral form `J` and integral vectors `v` and `w`, the matrix of the rank one map
`y ↦ h(w, y) v` is integral, where `h` is the form of `J`. -/
lemma IntegralPlace.isIntMatrix_vecMulVec_star_vecMul {J : Matrix ι ι A}
    (hJ : IsIntMatrix P.integers J) {v w : ι → A} (hv : v ∈ intVectors P.integers ι)
    (hw : w ∈ intVectors P.integers ι) : IsIntMatrix P.integers (vecMulVec v (star w ᵥ* J)) :=
  fun i j ↦ mul_mem (hv i)
    (sum_mem fun k _ ↦ mul_mem (isAdelic.toIsStarStable.star_mem (hw k)) (hJ k j))

omit [DecidableEq ι] in
/-- The flat chart `flatChart J β` of the quadric `h(v, v) = δ⁻¹ β` in a hyperbolic plane plus an
integral form `J`, with integral parameter `β`, maps `((t, w), a)` to an integral vector if `t` is a
unit of `P.integers` and `w` and `a` are integral. -/
lemma IntegralPlace.flatChart_mem_intVectors {J : Matrix ι ι A} (hJ : IsIntMatrix P.integers J)
    {β a : skewAdjoint A} (hβ : (β : A) ∈ P.integers) (ha : (a : A) ∈ P.integers)
    {t : Aˣ} (ht : t.val ∈ P.integers) (ht_inv : t⁻¹.val ∈ P.integers)
    {w : ι → A} (hw : w ∈ intVectors P.integers ι) :
    flatChart J β ((t, w), a) ∈ intVectors P.integers (Fin 2 ⊕ ι) := by
  obtain ⟨h_element, -, h_skew_inv, -⟩ := data_normalised (A := A)
  have h_norm : P.skewUnit⁻¹.val * β - star w ⬝ᵥ J *ᵥ w ∈ P.integers :=
    sub_mem (mul_mem h_skew_inv hβ) (star_dotProduct_mulVec_mem_integers hJ hw hw)
  have h_inv : Ring.inverse (star t.val) ∈ P.integers := by
    simpa using isAdelic.toIsStarStable.star_mem ht_inv
  have h_first : Ring.inverse (star t.val) * P.element *
      (P.skewUnit⁻¹.val * β - star w ⬝ᵥ J *ᵥ w) + t * a ∈ P.integers :=
    add_mem (mul_mem (mul_mem h_inv h_element) h_norm) (mul_mem ht ha)
  rintro (i | i)
  · fin_cases i
    · exact h_first
    · exact ht
  · exact hw i


/-- Let `T.splitGram` be unimodular over `P.integers`. Let `u` be an integral vector with
`star u ᵥ* T.splitGram` equal to the dual of the last frame vector z, and with z-coordinate `0`. Let
`e` be integral with z-coordinate `r`, a unit of `P.integers`. Then the scaled Eichler map along `u`
attached to `e` lies in `unitaryLevel P.integers 1 T.splitGram`, the group of integral
isometries. -/
lemma IntegralPlace.topEichler_mem_unitaryLevel_one (hT : IsUnimodular P.integers T.splitGram)
    {u : 𝔰.BesselIndex → A} (hu : u ∈ intVectors P.integers 𝔰.BesselIndex)
    (hu_dual : star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1)
    (hu_last : u (𝔰.besselFrame 𝔰.top) = 0) {e : 𝔰.BesselIndex → A}
    (he : e ∈ intVectors P.integers 𝔰.BesselIndex) {r : Aˣ} (hr_inv : r⁻¹.val ∈ P.integers)
    (he_last : e 𝔰.z = r) :
    topEichler hu_dual hu_last e ∈ unitaryLevel P.integers 1 T.splitGram := by
  -- The map is `1 + r⁻¹ (r u h(v, ·) - (v + s u) h(u, ·))` with `r⁻¹`, `v` and `s` integral.
  let z : 𝔰.BesselIndex → A := Pi.single (𝔰.besselFrame 𝔰.top) 1
  let s : A := star (e - z) ⬝ᵥ T.splitGram *ᵥ e -
    P.element * (star e ⬝ᵥ T.splitGram *ᵥ e - star z ⬝ᵥ T.splitGram *ᵥ z)
  have hJ : IsIntMatrix P.integers T.splitGram := hT.isIntMatrix
  have hz : z ∈ intVectors P.integers 𝔰.BesselIndex := single_mem_intVectors _
  have hv : e - z ∈ intVectors P.integers 𝔰.BesselIndex := sub_mem he hz
  have hs : s ∈ P.integers :=
    sub_mem (star_dotProduct_mulVec_mem_integers hJ hv he) (mul_mem data_normalised.1
      (sub_mem (star_dotProduct_mulVec_mem_integers hJ he he)
        (star_dotProduct_mulVec_mem_integers hJ hz hz)))
  have hru : e 𝔰.z • u ∈ intVectors P.integers 𝔰.BesselIndex := fun i ↦ mul_mem (he 𝔰.z) (hu i)
  have hvs : e - z + s • u ∈ intVectors P.integers 𝔰.BesselIndex :=
    fun i ↦ add_mem (hv i) (mul_mem hs (hu i))
  have h_inv : Ring.inverse (e 𝔰.z) ∈ P.integers := by rwa [he_last, Ring.inverse_unit]
  have h_int : IsIntMatrix P.integers (Ring.inverse (e 𝔰.z) •
      (vecMulVec (e 𝔰.z • u) (star (e - z) ᵥ* T.splitGram) -
        vecMulVec (e - z + s • u) (star u ᵥ* T.splitGram))) :=
    .smul h_inv (.sub (isIntMatrix_vecMulVec_star_vecMul hJ hru hv)
      (isIntMatrix_vecMulVec_star_vecMul hJ hvs hu))
  refine hT.mem_unitaryLevel (one_mem _) ?_
  rw [inv_one, one_smul, coe_topEichler, topEichlerMatrix, add_sub_cancel_left]
  have h_last : e (𝔰.besselFrame 𝔰.top) = e 𝔰.z := by simp
  rw [h_last]
  exact h_int

/-- Let the form be unimodular, let `u` be an integral isotropic vector dual to the last frame
vector z, and let `B` be an integral hyperbolic basis in which the z-coordinate is the coefficient
at the second vector of the first pair. Then there is a measure `θ` on the group of the top floor
(`T.floorGroup 𝔰.ϱ`) that `orbitPoint`, the map `σ ↦ σ⁻¹ z`, carries to the measure
`B.floorQuadricMeasure` of the top quadric, and that gives the group of integral isometries mass at
least the volume of `P.intUnits`, the set of units of the ring of integers. -/
lemma IntegralPlace.exists_measure_floorGroup_top (hT : IsUnimodular P.integers T.splitGram)
    {u : 𝔰.BesselIndex → A} (hu : u ∈ intVectors P.integers 𝔰.BesselIndex)
    (hu_dual : star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1)
    (hu_last : u (𝔰.besselFrame 𝔰.top) = 0) {B : HyperbolicBasis ι T m}
    (hB : IsIntMatrix P.integers B.basisMatrix)
    (hB_last : B.basisMatrix (inr ()) = Pi.single (inl 1) 1) :
    ∃ θ : Measure T.G,
      SFinite θ ∧
      (∀ᵐ x : T.G ∂θ, x ∈ T.floorGroup 𝔰.ϱ) ∧
      θ.map (orbitPoint 𝔰.top) = B.floorQuadricMeasure 𝔰.top ∧
      volume P.intUnits ≤ θ (unitaryLevel P.integers 1 T.splitGram) := by
  -- `θ` is the image of the chart measure under the Eichler maps `Φ p` attached to the points
  -- `φ p` of the quadric through z
  let J : Matrix (FloorPairs 𝔰.top m ⊕ ι ⊕ FloorPairs 𝔰.top m)
      (FloorPairs 𝔰.top m ⊕ ι ⊕ FloorPairs 𝔰.top m) A := hyperbolicGram (FloorPairs 𝔰.top m) 1
  let β : skewAdjoint A :=
    P.skewUnitMul (T.splitGram (𝔰.besselFrame 𝔰.top) (𝔰.besselFrame 𝔰.top))
  let φ (p : (A × (FloorPairs 𝔰.top m ⊕ ι ⊕ FloorPairs 𝔰.top m → A)) × skewAdjoint A) :
      𝔰.BesselIndex → A := B.floorBasis 𝔰.top *ᵥ flatChart J β p
  let Φ (p : (A × (FloorPairs 𝔰.top m ⊕ ι ⊕ FloorPairs 𝔰.top m → A)) × skewAdjoint A) : T.G :=
    topEichler hu_dual hu_last (φ p)
  have φ_last (t : A) (w) (a : skewAdjoint A) : φ ((t, w), a) 𝔰.z = t := by
    simp [φ, Matrix.mul_apply, mulVec, dotProduct, HyperbolicBasis.floorBasis, inclMatrix,
      flatChart, Matrix.one_apply, hB_last]
  have Φ_meas : Measurable Φ := (measurable_topEichler hu_dual hu_last).comp (by fun_prop)
  have Φ_orbit (t : A) (w) (a : skewAdjoint A) (ht : IsUnit t) :
      orbitPoint 𝔰.top (Φ ((t, w), a)) = φ ((t, w), a) := by
    have hJ : Jᴴ = J := by
      simp [J, fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
        conjTranspose_fromCols_eq_fromRows_conjTranspose]
    refine orbitPoint_topEichler hu_dual hu_last ?_ (by simpa [φ_last])
    rw [star_mulVec_dotProduct, mulVec_mulVec, mulVec_mulVec, B.gram_floorBasis,
      form_flatChart hJ ht]
    simp [β]
  -- integral parameters whose first coordinate is a unit of `integers` give integral isometries
  have Φ_box : (intUnits ×ˢ SetLike.coe (intVectors P.integers _)) ×ˢ
      {a : skewAdjoint A | a.val ∈ P.integers} ⊆ Φ ⁻¹' unitaryLevel P.integers 1 T.splitGram := by
    rintro ⟨⟨_, w⟩, a⟩ ⟨⟨⟨ht, t, ht_inv, rfl⟩, hw⟩, ha⟩
    have hJ : IsIntMatrix P.integers J := by simp [J, IsIntMatrix, Matrix.one_apply, ite_mem]
    obtain ⟨-, h_skew, -⟩ := data_normalised (A := A)
    have hβ : (β : A) ∈ P.integers := mul_mem h_skew (hT.isIntMatrix _ _)
    have φ_int : φ ((t, w), a) ∈ intVectors P.integers 𝔰.BesselIndex :=
      (isIntMatrix_floorBasis hB _).mulVec (flatChart_mem_intVectors hJ hβ ha ht ht_inv hw)
    exact topEichler_mem_unitaryLevel_one hT hu hu_dual hu_last φ_int ht_inv (φ_last t w a)
  refine ⟨(volume.prod P.skewMeasure).map Φ, inferInstance, ?_, ?_, ?_⟩
  · refine (ae_map_iff Φ_meas.aemeasurable measurableSet_floorGroup).2 (.of_forall fun p ↦ ?_)
    exact topEichler_mem_floorGroup hu_dual hu_last fun i hi ↦ B.floorBasis_mulVec_eq_zero _ hi
  · have h_chart : B.floorQuadricMeasure 𝔰.top = (volume.prod P.skewMeasure).map φ :=
      Measure.map_map (by fun_prop) (by fun_prop)
    rw [Measure.map_map (by fun_prop) Φ_meas, h_chart]
    -- the first coordinate is almost always a unit
    refine map_congr ?_
    filter_upwards [quasiMeasurePreserving_fst.ae (quasiMeasurePreserving_fst.ae ae_isUnit)]
      with ⟨⟨t, w⟩, a⟩ ht using Φ_orbit t w a ht
  · grw [← le_map_apply Φ_meas.aemeasurable, ← Φ_box]
    simp [volume_eq_prod, isOpen_isCompact_volume_intVectors, data_normalised]


/-- At the finite place `P`, let `N` be in `P.integers` with `star N = N`, let `g` be a unit of `A`
in `P.integers` with `star g = g`, and let the rank `𝔰.k` of X₀ be `|ι| + 2 m + 1`. Then the matrix
`latticeMiddleGram 𝔰 N` has a place datum `F : PlaceData ι (latticeMiddleGram 𝔰 N) m` with
`P.IsLatticeData F` and `F.levelUnit = g`. -/
theorem IntegralPlace.exists_isLatticeData {N : A}
    [IsHermitianUnit (latticeMiddleGram 𝔰 N).splitGram] (hN : N ∈ integers ∧ star N = N)
    (hg : g.val ∈ integers ∧ star g.val = g) (hm : 𝔰.k = Fintype.card ι + 2 * m + 1) :
    ∃ F : PlaceData ι (latticeMiddleGram 𝔰 N) m, P.IsLatticeData F ∧ F.levelUnit = g := by
  let T : 𝔰.Form A := latticeMiddleGram 𝔰 N
  let K : Subgroup T.G := unitaryLevel integers 1 T.splitGram
  have h_unimod : IsUnimodular integers T.splitGram :=
    (isUnimodular_latticeMiddleGram 𝔰 hN).splitGram
  -- pairing with `x` reads the coordinate at z
  let x : 𝔰.BesselIndex → A := Pi.single (𝔰.indexX₀ 𝔰.k₀) (-1)
  have hx : x ∈ intVectors integers 𝔰.BesselIndex := fun i ↦ by simp [x, Pi.single_apply, ite_mem]
  have hx_dual : star x ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1 := by
    simp [x, T, splitGram, latticeMiddleGram, diagonal, funext_iff]
  have hx_last : x (𝔰.besselFrame 𝔰.top) = 0 := by simp [x]
  obtain ⟨B, hB, hB_last⟩ := exists_isIntMatrix_hyperbolicBasis hN.1 hN.2 hm
  obtain ⟨θ, _, θ_mem, θ_map, θ_box⟩ :=
    exists_measure_floorGroup_top h_unimod hx hx_dual hx_last hB hB_last
  obtain ⟨η, _, η_box, η_spec⟩ := exists_right_invariant_measure_besselH (T := T)
  let F : PlaceData ι T m :=
    { B with
      topFloorMeasure := θ
      measureH := η
      levelUnit := g
      closePairs := P.congruentPairs 𝔰 g
      boxSet := K
      positions := {y⁻¹ * u * y | (y : T.G) (u ∈ T.besselU)} * unitaryLevel integers g T.splitGram
      neZero_measureH := ⟨fun h ↦ by simp [h] at η_box⟩
      topFloorMeasure_mem_and_map_eq := ⟨θ_mem, θ_map⟩
      measureH_mem_and_invariant_and_le_one := η_spec
      star_levelUnit := hg.2
      isOpen_closePairs_and_zero_mem_and_isCompact_closure :=
        isOpen_congruentPairs_and_isCompact_closure
      isCompact_boxSet_and_measurableSet_positions :=
                                            ⟨unitaryLevel_open_compact.2,
                                              unitaryLevel_open_compact.1.mul_left.measurableSet⟩ }
  exact ⟨F, ⟨⟨h_unimod, hB, hg⟩, ⟨θ_box, rfl, η_box, rfl, rfl⟩, x, hx_dual, hx_last⟩, rfl⟩

/-! ### Large lattice data: gauges and masses -/

namespace IntegralPlace.IsLargeLatticeData

variable {F : PlaceData ι T (m + 1)} [h : P.IsLargeLatticeData F]

/-- The close pairs of a large lattice datum are the pairs of integral vectors congruent modulo the
level. -/
theorem closePairs_eq : F.closePairs = P.congruentPairs 𝔰 F.levelUnit := by
  obtain ⟨-, -, -, h_close, -⟩ := h.volume_le_and_boxSet_closePairs_positions_eq
  exact h_close

/-- An integral unit `α` of `A` has `modulus α ≤ 1`, so `2 ≤ 2 / modulus α`. -/
lemma two_le_two_div_modulus {α : Aˣ} (hα : α.val ∈ integers) : 2 ≤ 2 / P.modulus α := by
  grw [modulus_le_one α hα, div_one]

/-- For a unit `α` of `A`, the inverse modulus of `α ^ j` is at most `(2 / modulus α) ^ j`. -/
lemma inv_modulus_pow_le (α : Aˣ) (j : ℕ) : (P.modulus (α ^ j).val)⁻¹ ≤ (2 / P.modulus α) ^ j := by
  grw [← one_le_two]
  simp [ENNReal.inv_pow]

include h in
/-- Let `F` be a large lattice datum with `m + 1` further pairs, so that the ideal zeta sum
`ζ = idealZeta P.integers m` is at most 2, and let `α` be an integral unit of `A`. The bound
`ζ * modulus (α ^ j) ^ (-n)`, which occurs for masses on quadrics, is at most `(2 / modulus α) ^ k`
if `j * n + 1 ≤ k`. -/
lemma idealZeta_mul_inv_modulus_pow_le {α : Aˣ} (hα : α.val ∈ integers) {j n k : ℕ}
    (hk : j * n + 1 ≤ k) :
    idealZeta P.integers m * (P.modulus (α ^ j).val)⁻¹ ^ n ≤ (2 / P.modulus α) ^ k := by
  have h_two : 2 ≤ 2 / P.modulus α := two_le_two_div_modulus hα
  have h_zeta : idealZeta P.integers m ≤ 2 := le_two_of_pow_le_ofReal h.zeta_le_and_le_card.1
  calc idealZeta P.integers m * (P.modulus (α ^ j).val)⁻¹ ^ n
    _ ≤ 2 / P.modulus α * ((2 / P.modulus α) ^ j) ^ n := by
      grw [h_zeta.trans h_two, inv_modulus_pow_le]
    _ = (2 / P.modulus α) ^ (j * n + 1) := by rw [← pow_mul, ← pow_succ']
    _ ≤ (2 / P.modulus α) ^ k := pow_le_pow_right₀ (one_le_two.trans h_two) hk

/-- The box of a large lattice datum is the group of integral isometries. -/
theorem boxSet_eq : F.boxSet = unitaryLevel integers 1 T.splitGram := by
  simp only [h.volume_le_and_boxSet_closePairs_positions_eq]

include h in
/-- If `F` is a large lattice datum (`P.IsLargeLatticeData F`), the Gram matrix `T.splitGram` is
hermitian and invertible over `integers`, that is, unimodular. -/
theorem isUnimodular_splitGram : IsUnimodular integers T.splitGram :=
  h.integral_data.1

/-- At a large lattice datum the basis matrix has entries in `integers`. -/
theorem isIntMatrix_basisMatrix : IsIntMatrix integers F.basisMatrix := by
  simp only [h.integral_data]

include h in
/-- At a large lattice datum with `m + 1` further hyperbolic pairs, the ideal zeta sum of
`P.integers` at `m` is at most `2`. -/
theorem idealZeta_le_two : idealZeta P.integers m ≤ 2 :=
  le_two_of_pow_le_ofReal h.zeta_le_and_le_card.1

include h in
/-- At a large lattice datum the form `T.splitGram` takes integral values on integral vectors. -/
theorem star_dotProduct_splitGram_mulVec_mem {v w : 𝔰.BesselIndex → A}
    (hv : v ∈ intVectors integers 𝔰.BesselIndex) (hw : w ∈ intVectors integers 𝔰.BesselIndex) :
    star v ⬝ᵥ T.splitGram *ᵥ w ∈ integers :=
  sum_mem fun i _ ↦ mul_mem (isAdelic.toIsStarStable.star_mem (hv i))
    (h.isUnimodular_splitGram.isIntMatrix.mulVec hw i)

include h in
/-- The quadrics of a block. The place datum has m + 1 further hyperbolic pairs, so a block has rank
2 m + 4. Its volume disintegrates along the standard form into an s-finite kernel, and on each
quadric the points y with u y integral, u a unit, have mass at most ζ |u|^(-(2 m + 3)), where ζ is
the ideal zeta sum `idealZeta P.integers m`. -/
lemma exists_kernel_isDisintegration_coordinateBox_le :
    ∃ q : ProbabilityTheory.Kernel (skewAdjoint A) (Fin F.blockRank → A),
      ProbabilityTheory.IsSFiniteKernel q ∧
      IsDisintegration volume 1 q ∧
      ∀ (β : skewAdjoint A) (u : Aˣ),
        q β (coordinateBox (Fin F.blockRank) {x : A | u.val * x ∈ P.integers}) ≤
          idealZeta P.integers m * (P.modulus u)⁻¹ ^ (2 * m + 3) :=
  exists_kernel_isDisintegration_le h.psi_add_star h.idealZeta_le_two
    (Fintype.card_fin _) (by lia)

/-- For a large lattice datum `F`, the elements of `F.productDifferences` are integral. These are
the numbers (h(ω₁, ω'₁) - h(ω₂, ω'₂)) / g, where g = `F.levelUnit`, h is the form `T.splitGram`, and
(ω₁, ω₂), (ω'₁, ω'₂) are pairs in `F.closePairs`. -/
lemma mem_of_mem_productDifferences {c : A} (hc : c ∈ F.productDifferences) : c ∈ P.integers := by
  obtain ⟨z, hz, z', hz', rfl⟩ : ∃ z ∈ F.closePairs, ∃ z' ∈ F.closePairs,
      c = F.levelUnit⁻¹ * (star z.1 ⬝ᵥ T.splitGram *ᵥ z'.1 - star z.2 ⬝ᵥ T.splitGram *ᵥ z'.2) := hc
  rw [closePairs_eq] at hz hz'
  obtain ⟨hz_int, hz_cong⟩ := hz
  obtain ⟨hz'_int, hz'_cong⟩ := hz'
  obtain ⟨-, -, hg, -⟩ := h.integral_data
  -- Write `z.1 - z.2 = g • b` and `z'.1 - z'.2 = g • d` with `b` and `d` integral.
  let b : 𝔰.BesselIndex → A := F.levelUnit⁻¹.val • (z.1 - z.2)
  let d : 𝔰.BesselIndex → A := F.levelUnit⁻¹.val • (z'.1 - z'.2)
  have h_gap : F.levelUnit⁻¹ * (star z.1 ⬝ᵥ T.splitGram *ᵥ z'.1 - star z.2 ⬝ᵥ T.splitGram *ᵥ z'.2) =
      star z.1 ⬝ᵥ T.splitGram *ᵥ d + star b ⬝ᵥ T.splitGram *ᵥ z'.1 -
        F.levelUnit * star b ⬝ᵥ T.splitGram *ᵥ d := by
    have h_star : star F.levelUnit⁻¹.val = F.levelUnit⁻¹.val := by
      simp [← inverse_star_unit, F.star_levelUnit]
    simp only [b, d, mulVec_sub, mulVec_smul, star_smul, star_sub, h_star, smul_sub,
      dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    grind [F.levelUnit.mul_inv]
  rw [h_gap]
  exact sub_mem (add_mem (h.star_dotProduct_splitGram_mulVec_mem hz_int hz'_cong)
    (h.star_dotProduct_splitGram_mulVec_mem hz_cong hz'_int))
    (mul_mem hg (h.star_dotProduct_splitGram_mulVec_mem hz_cong hz'_cong))

/-- Let `F` be a large lattice datum, `x` an integral isometry, and `z = y⁻¹ u y k` with `u` in
`T.besselU` and `k` in `F.congruenceSubgroup`. Let `v` have `ϱ` rows, and let `σ` split
`F.FreeIndex` into `3 ϱ` excepted indices and `d` others, listed by `σ ∘ inr`. There is a matrix `V`
invertible over the integers such that every integral combination `ω` of its columns at these `d`
indices is in `F.commonVectors x z v`: `v ω = 0`, and (x⁻¹ w, (x z)⁻¹ w) is a close pair for the
vector `w = F.orthonormalPart *ᵥ ω`. -/
lemma exists_intGL_mulVec_mem_commonVectors {x y u k : T.G}
    (hx : x ∈ unitaryLevel integers 1 T.splitGram)
    (hu : u ∈ T.besselU) (hk : k ∈ F.congruenceSubgroup) (v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A)
    {d : ℕ} (σ : SplitIndex 𝔰.ϱ (Fin 𝔰.ϱ) ⊕ Fin d ≃ F.FreeIndex) :
    ∃ V ∈ intGL F.FreeIndex P.integers, ∀ t ∈ intVectors P.integers (Fin d),
      V.val.submatrix id (σ ∘ inr) *ᵥ t ∈ F.commonVectors x (y⁻¹ * u * y * k) v := by
  -- A column operation `V` clears `3 ϱ` rows outside `3 ϱ` columns: the rows of `v`, the last `ϱ`
  -- rows of `N`, and the first `ϱ` rows of `(u⁻¹ - 1) N`. `Y` has the other columns.
  let N : Matrix 𝔰.BesselIndex F.FreeIndex A := (y * x⁻¹).val.val * F.orthonormalPart
  let C : Matrix (Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) F.FreeIndex A :=
    fromRows v (N ∘ inr ∘ inr ⊕ᵥ ((u⁻¹.val.val - 1) * N) ∘ inl)
  obtain ⟨V, hV, h_clear⟩ := isAdelic.isValuationPair.exists_mul_clear_cols C
    (.trans .inl σ.toEmbedding)
  let Y : Matrix F.FreeIndex (Fin d) A := V.val.submatrix id (σ ∘ inr)
  have h_zero (a : Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ ⊕ Fin 𝔰.ϱ) (j : Fin d) : (C * Y) a j = 0 :=
    h_clear a (σ (inr j)) (by simp)
  have h_orth : v * Y = 0 := ext fun a ↦ h_zero (inl a)
  -- `u⁻¹` fixes the columns of `N Y`: off the first rows it is the identity except in the last
  -- columns (`apply_inr_of_mem_besselU`), and these meet the last rows of `N Y`, which vanish
  have h_fix : (u⁻¹.val.val - 1) * N * Y = 0 := by
    ext (i | i) j
    · exact h_zero (inr (inr i)) j
    · have h_last (a : Fin 𝔰.ϱ) : (N * Y) (eStar a) j = 0 := h_zero (inr (inl a)) j
      have hu_inv : u⁻¹ ∈ T.besselU := inv_mem hu
      generalize u⁻¹ = u' at hu_inv ⊢
      simp [Matrix.mul_assoc, mul_apply (N := N * Y), apply_inr_of_mem_besselU hu_inv, h_last,
        Matrix.one_apply]
  -- so `(x z)⁻¹ = k⁻¹ y⁻¹ u⁻¹ y x⁻¹` acts on the columns as `k⁻¹ x⁻¹`
  let W : Matrix 𝔰.BesselIndex (Fin d) A := x⁻¹.val.val * (F.orthonormalPart * Y)
  have h_act : (x * (y⁻¹ * u * y * k))⁻¹.val.val * (F.orthonormalPart * Y) = k⁻¹.val.val * W := by
    rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h_fix
    calc
      _ = (k⁻¹ * y⁻¹).val.val * (u⁻¹.val.val * (N * Y)) := by simp [N, Matrix.mul_assoc]
      _ = (k⁻¹ * y⁻¹).val.val * (N * Y) := by rw [h_fix]
      _ = k⁻¹.val.val * W := by simp [N, W, Matrix.mul_assoc]
  have h_int : IsIntMatrix integers W :=
    (inv_mem hx).1.isIntMatrix.mul (by simp [mul_apply, h.isIntMatrix_basisMatrix _, Y,
      hV.isIntMatrix _, IsIntMatrix, mul_mem, sum_mem])
  have h_cong : IsIntMatrix integers (F.levelUnit⁻¹.val • (W - k⁻¹.val.val * W)) := by
    simpa [← smul_neg, Matrix.sub_mul, Units.smul_def] using ((inv_mem hk).2.mul h_int).neg
  refine ⟨V, hV, fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [mulVec_mulVec, h_orth, zero_mulVec]
  · rw [IsShortFrom, closePairs_eq]
    simp only [mulVec_mulVec]
    rw [h_act]
    exact ⟨h_int.mulVec ht, by simpa only [smul_mulVec, sub_mulVec] using h_cong.mulVec ht⟩
/-- Let `F` be a large lattice datum, `α` an integral unit of `A`, and `S` the sizes for which size
`j` means that `α ^ j * c` is integral. Let `x` be an integral isometry (`F.boxSet`), `z` a product
`y⁻¹ u y k` with `u` in `T.besselU` and `k` in `F.congruenceSubgroup` (`F.positions`), and
W = `F.commonVectors x z v`. Some measurable φ is an `IsCommonBound` with loss `2 / P.modulus α`:
φ(w) bounds 1 / vol ⟨w, W⟩ and the volume of the `c` with ⟨c w, W⟩ ⊆ `F.productDifferences`, and the
integral of `φ ^ F.volumeExponent` over the vectors of size `j` is at most
`(2 / P.modulus α) ^ (99 * 𝔰.n * (j + 1))`. -/
lemma exists_isCommonBound {α : Aˣ} (hα : α.val ∈ integers) {S : Size T}
    (hS : ∀ j : ℕ, S.ofSize j = {c : A | α ^ j * c ∈ integers}) {x z : T.G} (hx : x ∈ F.boxSet)
    (hz : z ∈ F.positions) (v : Matrix (Fin 𝔰.ϱ) F.FreeIndex A) :
    ∃ φ : (F.FreeIndex → A) → ℝ≥0∞,
      F.IsCommonBound S (2 / P.modulus α) (F.commonVectors x z v) φ := by
  -- Take for φ(u) the content index of `Yᴴ u`, where the integral combinations of the columns of
  -- `Y` are common vectors.
  obtain ⟨-, hm, h_card⟩ := h.zeta_le_and_le_card
  simp only [h.volume_le_and_boxSet_closePairs_positions_eq] at hx hz
  obtain ⟨_, ⟨y, n, hn, rfl⟩, k, hk, rfl⟩ := Set.mem_mul.1 hz
  have σ : SplitIndex 𝔰.ϱ (Fin 𝔰.ϱ) ⊕ Fin (F.volumeExponent + (m + 5)) ≃ F.FreeIndex :=
    equivOfCardEq <| by
      simp only [volumeExponent, Fintype.card_sum, Fintype.card_fin]
      lia
  obtain ⟨V, hV, h_common⟩ : ∃ V ∈ intGL F.FreeIndex P.integers,
      ∀ t ∈ intVectors P.integers (Fin (F.volumeExponent + (m + 5))),
        V.val.submatrix id (σ ∘ inr) *ᵥ t ∈ F.commonVectors x (y⁻¹ * n * y * k) v :=
    h.exists_intGL_mulVec_mem_commonVectors hx hn hk v σ
  set Y : Matrix F.FreeIndex (Fin (F.volumeExponent + (m + 5))) A := V.val.submatrix id (σ ∘ inr)
  have h_adj (u : F.FreeIndex → A) (t : Fin (F.volumeExponent + (m + 5)) → A) :
      star u ⬝ᵥ Y *ᵥ t = star (Yᴴ *ᵥ u) ⬝ᵥ t := by
    simp [star_mulVec, dotProduct_mulVec]
  refine ⟨fun u ↦ P.contentIndex 0 (Yᴴ *ᵥ u), by fun_prop, fun u ↦ le_iInf fun h_unit ↦ ?_,
    fun u ↦ le_iInf fun _ ↦ measure_mono fun c hc i ↦ ?_, fun j ↦ ?_⟩
  · -- if `t` is the content of `Yᴴ u`, the products of `u` with common vectors fill
    -- `star t • integers`
    obtain ⟨t, r, hr, hrt, ht⟩ : ∃ t : Aˣ, ∃ r ∈ intVectors integers _, r ⬝ᵥ Yᴴ *ᵥ u = t ∧
        ∀ c : A, (∀ j, c * (Yᴴ *ᵥ u) j ∈ integers) ↔ t * c ∈ integers := exists_content h_unit
    have h_vol : P.modulus (star t).val ≤ volume
        ((fun w : F.FreeIndex → A ↦ star u ⬝ᵥ w) '' F.commonVectors x (y⁻¹ * n * y * k) v) := by
      refine modulus_le_volume fun a ha ↦ ⟨Y *ᵥ (a • star r), h_common _ fun i ↦ ?_, ?_⟩
      · exact mul_mem ha (isAdelic.toIsStarStable.star_mem (hr i))
      · simp [star_dotProduct_star, h_adj, hrt, mul_comm]
    simpa [ht] using ENNReal.inv_le_inv.2 h_vol
  · -- test the condition on `c` at the `i`-th column of `Y`
    have h_mem : star (c • u) ⬝ᵥ Y *ᵥ Pi.single i 1 ∈ integers :=
      h.mem_of_mem_productDifferences (hc _ (h_common _ (single_mem_intVectors i)))
    have h_star : c * (Yᴴ *ᵥ u) i = star (star (c • u) ⬝ᵥ Y *ᵥ Pi.single i 1) := by
      rw [h_adj, dotProduct_single, mul_one, Pi.star_apply, star_star, mulVec_smul]
      rfl
    rw [h_star]
    exact isAdelic.toIsStarStable.star_mem h_mem
  · simp only [Size.vecsOfSize, hS]
    calc
      _ ≤ idealZeta P.integers m * (P.modulus (α ^ j).val)⁻¹ ^ (3 * 𝔰.ϱ + (m + 5)) :=
        lintegral_contentIndex_pow_le h.idealZeta_le_two σ 0 (α ^ j) hV
          ⟨by simp +arith, Fintype.card_fin _, by lia⟩
      _ ≤ (2 / P.modulus α) ^ (99 * 𝔰.n * (j + 1)) :=
        h.idealZeta_mul_inv_modulus_pow_le hα (by rw [Shape.n] at hm ⊢; nlinarith)

/-- The gauge of scale `α` at a large lattice datum, for an integral self-conjugate unit `α` of `A`:
a number `x` has size `j` if `α ^ j * x` is integral, and the field `loss` is `2 / P.modulus α`. -/
@[simp]
def gauge (α : Aˣ := 1) (hα : α.1 ∈ integers := by simp)
    (sα : star α.1 = α := by simp [*] <;> ring) :
    Gauge F where
  ofSize j := {x : A | α ^ j * x ∈ integers}
  loss := 2 / P.modulus α
  mul_mem_ofSize hx hy := by grind [integers.mul_mem hx hy]
  sum_mem_ofSize := by simp_all [pow_succ', mul_assoc, mul_sum, mul_mem, sum_mem]
  neg_mem_iff_and_star_mem_iff := by
             refine ⟨by simp, fun hx ↦ ?_, fun hx ↦ ?_⟩ <;> simpa [sα] using isAdelic.1.1 hx
  zero_one_mem_ofSize := by simp [pow_mem hα]
  splitGram_and_inv_mem := by
          simp [hα, h.integral_data.1.isIntMatrix _,
            h.integral_data.1.isUnit_det_and_isIntMatrix_inv.2 _, mul_mem]
  isCompact_ofSize j := isCompact_O.preimage_smul (α ^ j)
  two_le_loss := two_le_two_div_modulus hα
  loss_ne_top := by simp [div_eq_top]
  pairs_le := h.zeta_le_and_le_card.2.1
  one_le_kernelBound := by simp [data_normalised]
  levelUnit_mem_ofSize := by simp [hα, h.integral_data, mul_mem]
  hasMatrixSize_basisMatrix := by simp [hα, h.integral_data.2.1 _, Size.HasMatrixSize, mul_mem]
  traceOne_div_mem_ofSize := by simp [hα, data_normalised, mul_mem]
  hasMatrixSize_boxSet := by
          simp_all [h.volume_le_and_boxSet_closePairs_positions_eq, unitaryLevel, mem_intGL,
            -Sum.forall, Size.HasMatrixSize, mul_mem]
  mem_vecsOfSize_of_mem_closePairs ω₁ ω₂ hω := by
    rw [closePairs_eq] at hω
    exact ⟨fun i ↦ mul_mem (pow_mem hα 1) (hω.1 i), fun i ↦ mul_mem (pow_mem hα 1) (hω.2 i)⟩
  exists_unit_smul_mem_closePairs i hM := by
    -- Take `c = α ^ (i + 1)`: one factor `α` clears the denominator `g`, the others those of the
    -- vectors.
    have h_inv : (α : A) ^ (i + 2) * (α ^ (i + 1))⁻¹.val = α := by
      rw [pow_succ', mul_assoc, ← Units.val_pow_eq_pow_val, Units.mul_inv, mul_one]
    refine ⟨α ^ (i + 1), by rwa [Set.mem_ofPred, h_inv], fun ω₁ h₁ ω₂ h₂ ↦ ?_⟩
    rw [closePairs_eq]
    refine ⟨fun k ↦ by simpa [pow_succ', mul_assoc] using mul_mem hα (h₁ k), fun k ↦ ?_⟩
    convert integers.mul_mem hM (integers.sub_mem (h₁ k) (h₂ k)) using 1
    simp
    ring
  modulus_le j u hu := (inv_modulus_pow_le α j).trans'
         (by simpa [mul_comm] using modulus_le_one (α ^ j * u) hu)
  volume_ofSize_le j := (volume_setOf_mul_mem (α ^ j)).trans_le <| (inv_modulus_pow_le α j).trans <|
    by
           bound [one_le_two.trans (two_le_two_div_modulus hα)]
  two_mul_blockRank_le := by
    obtain ⟨-, hm, h_rank⟩ := h.zeta_le_and_le_card
    simp only [blockRank]
    lia
  exists_blockKernel := by
                 obtain ⟨l, h_sfinite, h_dis, h_mass⟩ :=
                   h.exists_kernel_isDisintegration_coordinateBox_le
                 exact ⟨l, h_sfinite, h_dis, fun β j ↦
                   (h_mass β (α ^ j)).trans
                     (h.idealZeta_mul_inv_modulus_pow_le hα (by simp only [blockRank]; nlinarith))⟩
  exists_commonBound _ hx _ hz := h.exists_isCommonBound hα (fun _ ↦ rfl) hx hz

/-- At a large lattice datum, let `y` and `γ⁻¹ y` be near at `l`: elements of
`partialUnitriangularGroup l` move them into the group of integral isometries. Then the leading
minors of order `j ≤ l` of the matrix of the products `h(f_a, γ f_b)` of the frame vectors are
integral. -/
theorem leadingMinor_mem_of_isNear {l : ℕ} {γ y : T.G} (hy : F.IsNear l y)
    (hγy : F.IsNear l (γ⁻¹ * y)) {j : Fin (𝔰.n + 1)} (hj : j.val ≤ l) :
    leadingMinor (T.frameGram (γ.val : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)) j ∈ P.integers := by
  -- In the gauge of scale `1` every size means integral.
  simpa [gauge] using
    (h.gauge 1 (one_mem P.integers) (star_one A)).leadingMinor_mem_ofSize_of_isNear hy hγy hj

include h in
/-- At a large lattice datum `F`, let `g` be an integral self-conjugate unit of `A`, `a < 𝔰.ϱ`, and
`S` a subgroup of the unipotent group `unipotentBelow a` of the floors below `a`. Some `u ∈ S` moves
the point `P.heisenbergElem a (v, β)` of the Heisenberg group of floor `a` into the congruence
subgroup `unitaryLevel integers g T.splitGram` exactly when every entry of `g⁻¹ * v` and also
`g⁻¹ * β` are integral. -/
lemma exists_mul_heisenbergElem_mem_unitaryLevel_iff
    (hg : g.val ∈ integers ∧ star g.val = g) (a : Fin 𝔰.ϱ) {S : Subgroup T.G}
    (hS : S ≤ unipotentBelow a) (v : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i} → A)
    (β : skewAdjoint A) :
    (∃ u ∈ S, u * P.heisenbergElem (T := T) a (v, β) ∈ unitaryLevel integers g T.splitGram) ↔
      (∀ i : {i : 𝔰.BesselIndex // a + 1 ≤ floorOf i}, g⁻¹.val * v i ∈ integers) ∧
      g⁻¹.val * (β : A) ∈ integers := by
  -- Write the extension of `v` by zero as `g • w`; then `v / g` is integral if and only if `w` is.
  obtain ⟨w, hw⟩ : ∃ w : 𝔰.BesselIndex → A, g • w = inclMatrix A Subtype.val *ᵥ v :=
    MulAction.surjective g _
  have h_int : (∀ i, g⁻¹.val * v i ∈ integers) ↔ w ∈ intVectors integers 𝔰.BesselIndex := by
    rw [← inv_smul_smul g w, hw]
    simp [inclMatrix_val_mulVec, dite_mem, intVectors, Units.smul_def]
  obtain ⟨hg_mem, hg_star⟩ := hg
  rw [h_int]
  constructor
  · -- In the gauge of scale `1`, the column of `e*_a` gives `w` and `(β - τ h(v, v)) / g`.
    rintro ⟨u, hu, -, h_cong⟩
    obtain ⟨hw_int, hβ⟩ := h.gauge.mem_vecsOfSize_and_mem_ofSize_of_heisenbergElem (i := 0) (u := g)
      (t := (v, β)) ⟨u, hS hu, fun i ↦ by simpa [Units.smul_def] using h_cong i (eStar a)⟩
    rw [← hw] at hw_int hβ
    replace hw_int : w ∈ intVectors integers 𝔰.BesselIndex := fun i ↦ by
      simpa [Units.smul_def] using hw_int i
    replace hβ : g⁻¹.val * (β : A) - P.element * g * star w ⬝ᵥ T.splitGram *ᵥ w ∈ integers := by
      simpa [Units.smul_def, mulVec_smul, hg_star, mul_sub, mul_left_comm, mul_assoc] using hβ
    have h_form : P.element * g * star w ⬝ᵥ T.splitGram *ᵥ w ∈ integers := by
      simp [data_normalised, mul_mem, hg_mem, h.star_dotProduct_splitGram_mulVec_mem hw_int hw_int]
    exact ⟨hw_int, by simpa using add_mem hβ h_form⟩
  · -- Take `u = 1`: with `e = e_a`, the Eichler map minus `1`, divided by `g`, is
    -- `(w - s e) h(e, ·) - e h(w, ·)` with `s` integral.
    rintro ⟨hw_int, hβ⟩
    let e : 𝔰.BesselIndex → A := Pi.single (inl a) 1
    let s : A := P.element * g * star w ⬝ᵥ T.splitGram *ᵥ w - g⁻¹.val * (β : A)
    have hJ : IsIntMatrix integers T.splitGram := h.isUnimodular_splitGram.isIntMatrix
    have he : e ∈ intVectors integers 𝔰.BesselIndex := single_mem_intVectors _
    have hs : s ∈ integers := sub_mem (mul_mem (mul_mem data_normalised.1 hg_mem)
      (h.star_dotProduct_splitGram_mulVec_mem hw_int hw_int)) hβ
    have hws : w - s • e ∈ intVectors integers 𝔰.BesselIndex :=
      fun i ↦ sub_mem (hw_int i) (mul_mem hs (he i))
    have h_param : P.element * star (g • w) ⬝ᵥ T.splitGram *ᵥ (g • w) - (β : A) = g * s := by
      simp [s, Units.smul_def, mulVec_smul, hg_star, mul_sub, mul_left_comm, mul_assoc]
    have h_eichler : eichlerMap T.splitGram e (-(g • w)) (g * s) - 1 =
        g • (vecMulVec (w - s • e) (star e ᵥ* T.splitGram) -
          vecMulVec e (star w ᵥ* T.splitGram)) := by
      ext i j
      simp only [eichlerMap, Units.smul_def, star_neg, star_smul, hg_star, neg_vecMul, smul_vecMul,
        Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.add_apply,
        Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    refine ⟨1, S.one_mem, h.isUnimodular_splitGram.mem_unitaryLevel hg_mem ?_⟩
    simp only [one_mul, TraceOne.heisenbergElem, ← hw]
    change IsIntMatrix integers (g⁻¹ • (eichlerMap T.splitGram e (-(g • w)) _ - 1))
    rw [h_param, h_eichler, inv_smul_smul]
    exact .sub (isIntMatrix_vecMulVec_star_vecMul hJ hws he)
      (isIntMatrix_vecMulVec_star_vecMul hJ he hw_int)

/-- For a large lattice datum, an integral self-conjugate unit `g` of `A`, `a < ϱ` and a subgroup
`S` of the unipotent group `unipotentBelow a` of the floors below `a`, the set `S·K(g)` has mass
`F.floorModulus a g = modulus g ^ (𝔰.k + 1 + 2(ϱ − a − 1) + 1/2)` for the measure
`heisenbergMeasure a` of the Heisenberg group of floor `a`. -/
theorem heisenbergMeasure_eq_floorModulus (hg : g.val ∈ integers ∧ star g.val = g) (a : Fin 𝔰.ϱ)
    {S : Subgroup T.G} (hS : S ≤ unipotentBelow a) :
    heisenbergMeasure a
        {y : U T.splitGram | ∃ u ∈ S, u * (y * 1) ∈ unitaryLevel integers g T.splitGram} =
      F.floorModulus a g := by
  -- `heisenbergMeasure a` is the image of `dv dβ` under the Heisenberg chart, and the preimage of
  -- `S·K(g)` is a box.
  have h_chart : P.heisenbergElem (T := T) a ⁻¹'
      {y : U T.splitGram | ∃ u ∈ S, u * (y * 1) ∈ unitaryLevel integers g T.splitGram} =
      Set.univ.pi (fun _ ↦ {x : A | g⁻¹.val * x ∈ integers}) ×ˢ
        {β : skewAdjoint A | g⁻¹.val * (β : A) ∈ integers} := by
    ext ⟨v, β⟩
    simpa only [Set.mem_preimage, Set.mem_ofPred, mul_one, Set.mem_prod, Set.mem_univ_pi] using
      h.exists_mul_heisenbergElem_mem_unitaryLevel_iff hg a hS v β
  have h_star : star g⁻¹.val = g⁻¹.val := by simp [← inverse_star_unit, hg]
  -- each coordinate of floor above `a` contributes `modulus g`, and `β` contributes
  -- `modulus g ^ (1 / 2)`
  rw [heisenbergMeasure, dite_eq_left a.is_lt,
    map_apply (by fun_prop) measurableSet_exists_mul_mem_level, h_chart, prod_prod,
    skewMeasure_setOf_mul_mem g⁻¹ h_star, volume_pi_pi, prod_const, Finset.card_univ,
    card_subtype_succ_le_floorOf_eq]
  simp [floorModulus, inv_rpow]

/-- For a large lattice datum `F` (`P.IsLargeLatticeData F`), a self-conjugate unit `g` of `A` in
`integers`, and `j ≤ 𝔰.ϱ` (the number of hyperbolic planes), the convolution
`ascConv heisenbergMeasure j` of the Heisenberg measures `heisenbergMeasure l`, `l < j`, gives the
congruence subgroup `unitaryLevel integers g T.splitGram` the mass `∏ l < j, F.floorModulus l g`.
Each factor is
|g|^(r+1/2), where r is the rank of the vector part of floor `l`. -/
theorem ascConv_unitaryLevel (hg : g.val ∈ integers ∧ star g.val = g) (j : ℕ) (hj : j ≤ 𝔰.ϱ) :
    ascConv heisenbergMeasure j (unitaryLevel integers g T.splitGram : Set (U T.splitGram)) =
      ∏ l ∈ Finset.range j, F.floorModulus l g := by
  induction j with
  | zero => simp [ascConv]
  | succ j ih =>
    -- unfolding splits off the factor `heisenbergMeasure j`, of mass `F.floorModulus j g`
    rw [prod_range_succ, ← ih (by lia), ← heisenbergMeasure_eq_floorModulus hg ⟨j, hj⟩ le_rfl,
      ← ascConv_mconv_unfolding]
    simp [ascConv]

variable {c : T.G} {θ : Measure T.G} [SFinite θ]

/-- Unfolding over all floors. Let `F` be a large lattice datum and `g` a self-conjugate unit of `A`
in `integers`. Write `K(g) = unitaryLevel integers g T.splitGram`. Then the convolution
`ascConv heisenbergMeasure (𝔰.ϱ + 2) ∗ₘ θ` gives the coset `K(g) c⁻¹` the mass
`∏ l < 𝔰.ϱ, F.floorModulus l g` times the `θ`-mass of `𝖴 K(g) c⁻¹`. Here `𝖴` is the Bessel unipotent
group `T.besselU`. -/
theorem ascConv_mconv_unitaryLevel_coset (hg : g.val ∈ integers ∧ star g.val = g) :
    (ascConv heisenbergMeasure (𝔰.ϱ + 2) ∗ₘ θ)
        {y : T.G | y * c ∈ unitaryLevel integers g T.splitGram} =
      (∏ l ∈ Finset.range 𝔰.ϱ, F.floorModulus l g) *
        θ {y : T.G | ∃ u ∈ T.besselU, u * (y * c) ∈ unitaryLevel integers g T.splitGram} := by
  -- The two top floors contribute the unit mass at `1`.
  have h_top : ascConv (T := T) heisenbergMeasure (𝔰.ϱ + 2) = ascConv heisenbergMeasure 𝔰.ϱ := by
    simp [ascConv]
  rw [ascConv_mconv_unfolding, h_top, h.ascConv_unitaryLevel hg 𝔰.ϱ le_rfl]
  simp [unipotentBelow_eq_besselU]

/-- For a large lattice datum `F` at a finite place, the box `F.boxSet`, which is the group of
integral isometries, has `F.groupMeasure`-mass at most `1 + 2⁻¹ ^ n`, where `n = ϱ + 1`. -/
theorem groupMeasure_boxSet_le : F.groupMeasure F.boxSet ≤ ENNReal.ofReal (1 + 2⁻¹ ^ 𝔰.n) := by
  -- Unfolding at level `1` bounds `F.groupMeasure F.boxSet` by the mass of the frames near the box,
  -- and each of the `𝔰.n` floors contributes at most `idealZeta P.integers m`: for the gauge of
  -- scale `1` every `ofSize j` is `P.integers`, of volume `1`.
  have h_floor (l : Fin 𝔰.n) : F.FloorMassLe l (idealZeta P.integers m) 1 := by
    -- Solve the equation in a block. The other coordinates are free in `P.integers`.
    obtain ⟨q, _, h_dis, h_mass⟩ := h.exists_kernel_isDisintegration_coordinateBox_le
    obtain ⟨blk', blk, h_inj⟩ : ∃ blk' blk : Fin F.blockRank → ι,
        Function.Injective (F.freeIndex ⊕ᵥ (blk' ⊕ᵥ blk)) := h.gauge.exists_blocks
    have h_blocks : Function.Injective (blk' ⊕ᵥ blk) := h_inj.comp inr_injective
    have h_blk : Function.Injective blk := h_blocks.comp inr_injective
    -- `mid` places the orthonormal indices among the indices of the hyperbolic form
    let mid : ι → FloorPairs l (m + 1) ⊕ ι ⊕ FloorPairs l (m + 1) := inr ∘ inl
    have h_mid : Function.Injective mid := inr_injective.comp inl_injective
    refine h.gauge.floorMassLe_one_of_le l fun β ↦ ?_
    have h_solved : IsSolvedIn (inr ∘ mid ∘ blk)
        (quadricMeasure (hyperbolicGram (FloorPairs l (m + 1)) (1 : Matrix ι ι A)) β) P.integers
        (idealZeta P.integers m) := by
      refine h_dis.isSolvedIn_quadricMeasure (h_mass := fun b ↦ by simpa using h_mass b 1)
        (hT := ?_) (h_inj := h_mid.comp h_blk) (h_orth := ?_) β
      · simp [fromBlocks_conjTranspose, conjTranspose_fromRows_eq_fromCols_conjTranspose,
          conjTranspose_fromCols_eq_fromRows_conjTranspose]
      · rintro i (k | k | k) <;> simp [mid, Matrix.one_apply]
    have h_disjoint : Function.Injective ((inr ∘ mid ∘ blk') ⊕ᵥ (inr ∘ mid ∘ blk) :
        Fin F.blockRank ⊕ Fin F.blockRank →
          Fin 2 ⊕ FloorPairs l (m + 1) ⊕ ι ⊕ FloorPairs l (m + 1)) := by
      simpa only [comp_elim] using inr_injective.comp (h_mid.comp h_blocks)
    simpa [SemilocalField.volume_O, volume_coordinateBox, Size.vecsOfSize, -Sum.forall] using!
      h_solved.setLIntegral_le isOpen_O.measurableSet h_disjoint measurable_one
  calc F.groupMeasure F.boxSet
    _ ≤ F.quotientMeasureFrom 0 {g : T.G | F.IsNear (𝔰.ϱ + 2) (g * 1)} := by
      simpa [h.boxSet_eq, floorModulus, IsNear, partialGroupMeasure_zero_eq] using
        (h.ascConv_mconv_unitaryLevel_coset (g := 1) (c := 1) (by simp)).le
    _ ≤ idealZeta P.integers m ^ 𝔰.n := F.quotientMeasureFrom_isNear_le h_floor 0 1
    _ ≤ ENNReal.ofReal (1 + 2⁻¹ ^ 𝔰.n) := h.zeta_le_and_le_card.1

/-- The box of a large lattice datum is a group, so its mass for a convolution `σ ∗ₘ θ` is at least
the product of its masses for `σ` and `θ`. -/
lemma mul_le_mconv_boxSet (σ θ : Measure T.G) [SFinite θ] :
    σ F.boxSet * θ F.boxSet ≤ (σ ∗ₘ θ) F.boxSet := by
  grw [← prod_prod, mconv, ← le_map_apply (by fun_prop), boxSet_eq]
  exact measure_mono fun z ⟨hz₁, hz₂⟩ ↦ mul_mem hz₁ hz₂

/-- Let `F` be a large lattice datum. The measure `weylLaw l` is the image of `modulus c ^ d dc`
under `c ↦ (floorWeyl l c)⁻¹`, for a natural number `d` depending on the floor `l`. It gives the box
`F.boxSet` mass at least the volume of `P.intUnits`, the set of units of the ring of integers. -/
lemma volume_intUnits_le_weylLaw_boxSet (l : ℕ) : volume P.intUnits ≤ weylLaw l F.boxSet := by
  -- For a unit `u` of `P.integers` the Weyl element `floorWeyl l u` lies in the box, and the
  -- density `modulus u ^ d` is at least `1`.
  have h_mem : P.intUnits ⊆ (fun c : A ↦ (floorWeyl (T := T) l c)⁻¹) ⁻¹' F.boxSet := by
    rintro _ ⟨hu, u, hu_inv, rfl⟩
    rw [boxSet_eq]
    refine inv_mem (h.isUnimodular_splitGram.mem_unitaryLevel integers.one_mem ?_)
    simp [floorWeyl, weylOn, Matrix.one_apply, hu, hu_inv, IsIntMatrix, ite_mem,
      IsStarStable.star_mem, sub_mem]
  have h_density (d : ℕ) : ∀ c ∈ P.intUnits, 1 ≤ P.modulus c ^ d := by
    rintro _ ⟨-, u, hu_inv, rfl⟩
    exact one_le_pow₀ (by simpa using modulus_le_one _ hu_inv)
  let d : ℕ := 𝔰.k + 1 + 2 * (𝔰.ϱ - (l + 1))
  calc volume P.intUnits
    _ ≤ ∫⁻ c in P.intUnits, P.modulus c ^ d := by
      grw [← meas_le_lintegral₀ (by fun_prop) (h_density d), restrict_eq_self _ subset_rfl]
    _ ≤ volume.withDensity (fun c : A ↦ P.modulus c ^ d) P.intUnits := withDensity_apply_le _ _
    _ ≤ volume.withDensity (fun c : A ↦ P.modulus c ^ d)
          ((fun c : A ↦ (floorWeyl (T := T) l c)⁻¹) ⁻¹' F.boxSet) := measure_mono h_mem
    _ ≤ weylLaw l F.boxSet := le_map_apply (by fun_prop) _

/-- Let `F` be a large lattice datum at a finite place. Let `l + i = 𝔰.ϱ`. The measure
`F.partialGroupMeasure l (i + 2)` convolves the Heisenberg and floor measures of the `i + 2` floors
from `l` on. It gives the box `F.boxSet`, the group of integral isometries, mass at least
`volume P.intUnits ^ (i + 1)`. -/
theorem le_partialGroupMeasure_boxSet (i l : ℕ) (hl : l + i = 𝔰.ϱ) :
    volume P.intUnits ^ (i + 1) ≤ F.partialGroupMeasure l (i + 2) F.boxSet := by
  -- Each floor contributes at least `volume P.intUnits`; descend from the top floor.
  induction i generalizing l with
  | zero =>
    obtain rfl : l = 𝔰.ϱ := hl
    obtain ⟨h_theta, -, h_norm, -⟩ := h.volume_le_and_boxSet_closePairs_positions_eq
    calc volume P.intUnits ^ (0 + 1)
      _ ≤ F.measureH F.boxSet * F.topFloorMeasure F.boxSet := by simpa [h_norm] using h_theta
      _ ≤ (F.measureH ∗ₘ F.topFloorMeasure) F.boxSet := h.mul_le_mconv_boxSet _ _
      _ = F.partialGroupMeasure 𝔰.ϱ (0 + 2) F.boxSet := by simp [descConv, floorMeasure]
  | succ i ih =>
    have h_eta : heisenbergMeasure l F.boxSet = 1 := by
      simpa [floorModulus, ← h.boxSet_eq] using
        h.heisenbergMeasure_eq_floorModulus (g := 1) (by simp) ⟨l, by lia⟩ bot_le
    calc volume P.intUnits ^ (i + 1 + 1)
      _ ≤ F.partialGroupMeasure (l + 1) (i + 2) F.boxSet *
          (heisenbergMeasure l F.boxSet * (weylLaw l F.boxSet * heisenbergMeasure l F.boxSet)) := by
        rw [h_eta, mul_one, one_mul, pow_succ]
        exact mul_le_mul' (ih (l + 1) (by lia)) (h.volume_intUnits_le_weylLaw_boxSet l)
      _ ≤ (F.partialGroupMeasure (l + 1) (i + 2) ∗ₘ
            (heisenbergMeasure l ∗ₘ (weylLaw l ∗ₘ heisenbergMeasure l))) F.boxSet := by
        grw [h.mul_le_mconv_boxSet, h.mul_le_mconv_boxSet, h.mul_le_mconv_boxSet]
      _ = F.partialGroupMeasure l (i + 1 + 2) F.boxSet := by
        have hl_lt : l < 𝔰.ϱ := by lia
        simp [descConv, floorMeasure, hl_lt]

/-- For a large lattice datum, `F.groupMeasure` is a Haar measure. -/
instance isHaarMeasure_groupMeasure : F.groupMeasure.IsHaarMeasure := by
  -- `F.groupMeasure` is right invariant, so it is a multiple `d • ν` of a unimodular Haar measure
  obtain ⟨ν, hν_haar, hν_right⟩ : ∃ ν : Measure T.G, ν.IsHaarMeasure ∧ ν.IsMulRightInvariant :=
    h.unimodular
  obtain ⟨d, hd⟩ : ∃ d : ℝ≥0∞, F.groupMeasure = d • ν :=
    exists_eq_smul_haar ν F.isMulRightInvariant_groupMeasure
  have hd_zero : d ≠ 0 := fun h_zero ↦ by simp [h_zero, partialGroupMeasure_ne_zero] at hd
  -- `d` is finite because the box has finite mass for `F.groupMeasure` and non-zero mass for `ν`
  have hd_top : d ≠ ∞ := by
    rintro rfl
    have h_box : ν F.boxSet ≠ 0 := by
      rw [boxSet_eq]
      exact unitaryLevel_open_compact.1.measure_ne_zero ν ⟨1, one_mem _⟩
    simpa [hd, h_box] using h.groupMeasure_boxSet_le
  rw [hd]
  exact .smul _ hd_zero hd_top

end IntegralPlace.IsLargeLatticeData

end New.Floors

end
