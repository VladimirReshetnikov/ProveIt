import New.Spanning.Frames.StandardLevel

/-!
# Fiber measures of the standard form, and the top quadric by its last entry

At a finite place and in rank at least two, the volume of `κ → A` disintegrates along `ω ↦ ω* ω`
into the fiber measures `Place.normFiberMeasure`. The main result,
`HyperbolicBasis.integral_floorQuadricMeasure_top`, writes the measure of the quadric of vectors of
norm `-N` in `X₀ ⊕ A z` as an integral, over the last entry `t = ⟨z, y⟩` of a vector `y`, of the
fiber measures of the spheres `ω* ω = t t̄ / N - N` in `X₀`.

Notions from other files:

* `Place A`: a locally compact star ring with Haar volume, a multiplicative `modulus`, skew unit
  `δ = skewUnit` and Haar measure `skewMeasure` on the skew elements; `IntegralPlace A` is a finite
  place, or a finite set of finite places read as one ring.
* `P.IsDisintegration μ J l`: the measures `l b`, for skew `b`, are the fiber measures of `μ` on the
  quadrics `x* J x = δ⁻¹ b` and depend continuously on `b`.
* `flatChart S b`, `P.quadricMeasure S b`: coordinates and measure on the quadric of norm `δ⁻¹ b`
  for `planeSumGram S`, the Gram matrix of a hyperbolic plane plus `S`.
* `latticeMiddleGram 𝔰 N`: the Gram matrix of `X₀ ⊕ A z`, where `X₀` has an orthonormal basis `x_i`
  indexed by `𝔰.κ` and `z` has norm `-N`, `N = π π̄`, in the lattice basis `x_i` (`i ≠ k₀`),
  `v = x_{k₀} / π̄ + z / N`, `z`. For such a Gram matrix `T : 𝔰.Form A`, the matrix `T.splitGram`
  is that of the whole space, with hyperbolic planes added.
* `vectorOfLastEntry π t x`: the vector `y = x - (π π̄)⁻¹ t z` of `X₀ ⊕ A z`, in the lattice basis
  of the whole space. Its pairing `⟨z, y⟩` with the last frame vector `z`, called its last entry, is
  `t`.

## Relation to the literature

See `New.Spanning.MainTerm.EnergyEstimate` for related work.
-/

noncomputable section
namespace New.Floors
open Matrix MeasureTheory Measure ENNReal NNReal Sum Fintype FloorGroups Place SemilocalField
  Function Filter Topology

section Place
variable {A ι κ : Type} [CommRing A] [StarRing A] [TopologicalSpace A] [MeasureSpace A]
  [P : Place A] [Fintype ι] [Fintype κ] {𝔰 : Shape} {π : Aˣ} {t : A}

/-- Let the measures `l b`, indexed by the skew elements `b` of the place `A`, disintegrate `μ`
along the form `J`. For a continuous complex function `f` of compact support, the integral of `f`
against `l b` depends continuously on `b`. -/
lemma Place.IsDisintegration.continuous_integral {μ : Measure (ι → A)} {J : Matrix ι ι A}
    {l : skewAdjoint A → Measure (ι → A)} (h : P.IsDisintegration μ J l) {f : (ι → A) → ℂ}
    (hf : Continuous f) (h_supp : HasCompactSupport f) :
    Continuous fun b : skewAdjoint A ↦ ∫ x : ι → A, f x ∂l b := by
  -- Split `f` into real and imaginary parts, and these into positive and negative parts.
  have f_int (b : skewAdjoint A) : Integrable f (l b) :=
    have : IsFiniteMeasureOnCompacts (l b) := h.isFiniteMeasureOnCompacts b
    hf.integrable_of_hasCompactSupport h_supp
  have pos_part (φ : ℂ →L[ℝ] ℝ) :
      Continuous fun b : skewAdjoint A ↦ (∫⁻ x, ENNReal.ofReal (φ (f x)) ∂l b).toReal := by
    have h_supp_pos : HasCompactSupport fun x ↦ (φ (f x)).toNNReal :=
      h_supp.comp_left (g := fun w : ℂ ↦ (φ w).toNNReal) (by simp)
    obtain ⟨h_cont, h_fin⟩ : (Continuous fun b ↦ ∫⁻ x, (φ (f x)).toNNReal ∂l b) ∧
        ∀ b, ∫⁻ x, (φ (f x)).toNNReal ∂l b < ∞ :=
      h.continuous_and_lt_top (by fun_prop) h_supp_pos
    exact continuousOn_toReal.comp_continuous h_cont fun b ↦ (h_fin b).ne
  have real_part (φ : ℂ →L[ℝ] ℝ) : Continuous fun b : skewAdjoint A ↦ ∫ x, φ (f x) ∂l b := by
    have neg_part : Continuous fun b ↦ (∫⁻ x, ENNReal.ofReal (-φ (f x)) ∂l b).toReal := by
      simpa using pos_part (-φ)
    have h_split (b : skewAdjoint A) : ∫ x, φ (f x) ∂l b =
        (∫⁻ x, ENNReal.ofReal (φ (f x)) ∂l b).toReal -
          (∫⁻ x, ENNReal.ofReal (-φ (f x)) ∂l b).toReal :=
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (φ.integrable_comp (f_int b))
    exact ((pos_part φ).sub neg_part).congr fun b ↦ (h_split b).symm
  have h_re : Continuous fun b ↦ ((∫ x, (f x).re ∂l b : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (real_part Complex.reCLM)
  have h_im : Continuous fun b ↦ ((∫ x, (f x).im ∂l b : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (real_part Complex.imCLM)
  exact (h_re.add (h_im.mul_const Complex.I)).congr fun b ↦ integral_re_add_im (f_int b)

variable (κ) in
/-- The fiber measures `dω / d⟨ω, ω⟩` of the standard hermitian form on `κ → A`: the disintegration
of the volume along `ω ↦ ω* ω`, if there is one (it is unique by `IsDisintegration.unique`), and an
arbitrary family otherwise. At a finite place and in rank at least two the disintegration exists
(`IntegralPlace.isDisintegration_normFiberMeasure`), and the measure at `b` lives on the quadric
`ω* ω = δ⁻¹ b`, where `δ = P.skewUnit` (`IntegralPlace.ae_normFiberMeasure_dotProduct_eq`). -/
def Place.normFiberMeasure [DecidableEq κ] : skewAdjoint A → Measure (κ → A) :=
  Classical.epsilon fun l : skewAdjoint A → Measure (κ → A) ↦
    P.IsDisintegration volume (1 : Matrix κ κ A) l

/-- The skew element `δ α`, where `δ = P.skewUnit`, `α = t t̄ / N - N` and `N = π π̄`; it is the
index in `Place.normFiberMeasure` of the sphere `ω* ω = α`. With `z` the last frame vector, of norm
`-N` and orthogonal to `X₀`, the vector `y = ω - N⁻¹ t z` has `⟨z, y⟩ = t`, and it has norm `-N` if
and only if `ω` lies on this sphere. -/
def lastEntrySphereIndex (π : Aˣ) (t : A) : skewAdjoint A :=
  P.skewUnitMul (↑(π * star π)⁻¹ * t * star t - π * star (π : A)) <| by
    simp [mul_comm, mul_left_comm, mul_assoc]

/-- The skew element `lastEntrySphereIndex π t = δ (t t̄ / N - N)`, where `δ = P.skewUnit` and
`N = π π̄`, depends continuously on `t`. -/
@[fun_prop] lemma continuous_lastEntrySphereIndex :
    Continuous (lastEntrySphereIndex π : A → skewAdjoint A) := by
  unfold lastEntrySphereIndex skewUnitMul
  fun_prop

/-- For a unit `u` and an s-finite measure `ζ`, the map
`(t, (s, w), z) ↦ ((s, (w, u t)), z)`, which appends `u t` to the vector `w`, carries
`modulus u • dt` times `ds dw dζ` to the volume of `A × (κ ⊕ Unit → A)` times `ζ`. -/
lemma measurePreserving_append_last {Z : Type} [MeasurableSpace Z] (ζ : Measure Z) [SFinite ζ]
    (u : Aˣ) :
    MeasurePreserving
      (fun ((t, (s, w), z) : A × (A × (κ → A)) × Z) ↦ ((s, w ⊕ᵥ fun _ : Unit ↦ u * t), z))
      ((P.modulus u • volume).prod (volume.prod ζ)) (volume.prod ζ) := by
  classical
  let ν : Measure A := P.modulus u • volume
  have h_scale : MeasurePreserving (fun t : A ↦ u * t) ν volume := by
    refine ⟨by fun_prop, ?_⟩
    calc
      ν.map (fun t : A ↦ u * t) = P.modulus u • (P.modulus u)⁻¹ • volume := by
        simp [ν, (measurable_const_mul (u : A)).aemeasurable, P.map_mul_volume]
      _ = volume := by simp [smul_smul, ENNReal.mul_inv_cancel]
  have h_last : MeasurePreserving (fun (t : A) (_ : Unit) ↦ u * t) ν volume :=
    (volume_preserving_funUnique Unit A).symm.comp h_scale
  have h_join : MeasurePreserving (fun p : (κ → A) × A ↦ p.1 ⊕ᵥ fun _ : Unit ↦ u * p.2)
      (volume.prod ν) volume :=
    measurePreserving_sumElim.comp ((MeasurePreserving.id volume).prod h_last)
  have h_rotate : MeasurePreserving
      (fun (t, s, w) ↦ (s, w, t) : A × A × (κ → A) → A × (κ → A) × A)
      (ν.prod volume) (volume.prod (volume.prod ν)) :=
    (measurePreserving_prodAssoc volume volume ν).comp measurePreserving_swap
  have h_vec : MeasurePreserving
      (fun (t, s, w) ↦ (s, w ⊕ᵥ fun _ ↦ u * t) : A × A × (κ → A) → A × (κ ⊕ Unit → A))
      (ν.prod volume) volume :=
    ((MeasurePreserving.id volume).prod h_join).comp h_rotate
  exact (h_vec.prod (.id ζ)).comp (measurePreserving_prodAssoc ν volume ζ).symm

/-- The top quadric of the form `T.splitGram`: the vectors of `X₀ ⊕ A z`, that is with no component
along the hyperbolic pairs (the indices of floor less than `𝔰.ϱ`), that have the norm of the last
frame vector `z`. -/
def lastVectorQuadric (T : 𝔰.Form A) : Set (𝔰.BesselIndex → A) :=
  {e | (∀ i : 𝔰.BesselIndex, floorOf i < 𝔰.ϱ → e i = 0) ∧
    star e ⬝ᵥ T.splitGram *ᵥ e = T.splitGram 𝔰.z 𝔰.z}

/-- For fixed `t`, the map `vectorOfLastEntry π t` is a closed embedding. It sends `x` in
`X₀ = (𝔰.κ → A)` to `x - (π π̄)⁻¹ t z`. -/
lemma isClosedEmbedding_vectorOfLastEntry :
    IsClosedEmbedding (vectorOfLastEntry π t : (𝔰.κ → A) → 𝔰.BesselIndex → A) := by
  -- The coordinates along `X₀` in the standard basis give a continuous left inverse.
  let proj (e : 𝔰.BesselIndex → A) (i : 𝔰.κ) : A :=
    ((besselLatticeBasis 𝔰 π : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ e) (𝔰.indexX₀ i)
  have h_left : LeftInverse proj (vectorOfLastEntry π t) := fun x ↦ by
    have h_std : (besselLatticeBasis 𝔰 π : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A) *ᵥ
        vectorOfLastEntry π t x =
          (0 : Fin 𝔰.ϱ → A) ⊕ᵥ ((x ⊕ᵥ fun _ : Unit ↦ -(π * star π)⁻¹ * t) ⊕ᵥ 0) := by
      simp [vectorOfLastEntry]
    ext i
    simp [proj, h_std]
  have h_cont : Continuous proj := by fun_prop
  exact h_left.isClosedEmbedding h_cont (by fun_prop)

end Place

section TailBasis
variable {A : Type} [CommRing A] [StarRing A] {𝔰 : Shape} {π : Aˣ} {t : A}

variable (𝔰 π) in
/-- The orthonormal basis of `X₀` followed by `π⁻¹ z`, in the coordinates of the lattice basis. -/
def middleBasisMatrix : Matrix 𝔰.MiddleIndex (𝔰.κ ⊕ Unit) A :=
  (middleInclusionMatrix 𝔰 π).fromCols (fromRows 0 (scalar Unit (↑π⁻¹ : A)))

/-- Let `X₀`, of index set `𝔰.κ`, have the orthonormal basis `x_i`, let `z` be orthogonal to `X₀` of
norm `-N`, where `π π̄ = N`, and let `k₀ = 𝔰.k₀` be the marked index. The form
`latticeMiddleGram 𝔰 N` of `X₀ ⊕ A z` is written in the lattice basis `x_i` (`i ≠ k₀`),
`v = x_{k₀} / π̄ + z / N`, `z`. In the basis `middleBasisMatrix`, made of the `x_i` and `π⁻¹ z`,
its Gram matrix is `diag(1, …, 1, -1)`. -/
lemma gram_middleBasisMatrix {N : A} (hN : π * star (π : A) = N) :
    (middleBasisMatrix 𝔰 π)ᴴ * latticeMiddleGram 𝔰 N * middleBasisMatrix 𝔰 π = fromBlocks 1 0 0
      (-1) := by
  have h_inv : star (↑π⁻¹ : A) * star (π : A) = 1 := by rw [← star_mul, π.mul_inv, star_one]
  have h_cancel : star (↑π⁻¹ : A) * N = π := by rw [← hN, mul_left_comm, h_inv, mul_one]
  -- The pairings of the new basis with the lattice basis: only `x_{k₀} = π̄ v - π⁻¹ z` and `π⁻¹ z`
  -- pair with `v` (at the index `k₀`), and only `π⁻¹ z` pairs with `z`.
  have h_pairing : (middleBasisMatrix 𝔰 π)ᴴ * latticeMiddleGram 𝔰 N =
      fromBlocks (Filling.scaleAt (star (↑π⁻¹ : A)) 𝔰.k₀) 0
        (of fun _ j ↦ if j = 𝔰.k₀ then -star (↑π⁻¹ : A) else 0) (of fun _ _ ↦ -(π : A)) := by
    ext (i | ⟨⟩) (j | ⟨⟩)
    · by_cases hi : i = 𝔰.k₀ <;> by_cases hj : j = 𝔰.k₀ <;>
        simp [middleBasisMatrix, middleInclusionMatrix, latticeMiddleGram, mul_apply, diagonal,
          apply_ite star,
          hi, hj, eq_comm]
    · by_cases hi : i = 𝔰.k₀ <;>
        simp [middleBasisMatrix, middleInclusionMatrix, latticeMiddleGram, mul_apply, diagonal,
          apply_ite star,
          h_cancel, hi, eq_comm]
    · simp [middleBasisMatrix, latticeMiddleGram, mul_apply]
    · simp [middleBasisMatrix, latticeMiddleGram, mul_apply, h_cancel]
  -- Multiply by the new basis: the `x_i` are orthonormal and orthogonal to `π⁻¹ z`, whose norm
  -- is `-π π⁻¹ = -1`.
  rw [h_pairing]
  ext (i | ⟨⟩) (j | ⟨⟩)
  · by_cases hi : i = 𝔰.k₀ <;> by_cases hj : j = 𝔰.k₀ <;>
      simp [middleBasisMatrix, middleInclusionMatrix, mul_apply, diagonal, one_apply, h_inv, hi, hj,
        eq_comm]
  · simp [middleBasisMatrix, mul_apply]
  · by_cases hj : j = 𝔰.k₀ <;>
      simp [middleBasisMatrix, middleInclusionMatrix, mul_apply, diagonal, h_inv, hj]
  · simp [middleBasisMatrix, mul_apply]

/-- In the basis `middleBasisMatrix`, the orthonormal basis of `X₀` followed by `π⁻¹ z`, the vector
`vectorOfLastEntry π t x = x - (π π̄)⁻¹ t z` has the coordinates `x` on `X₀` and `-π̄⁻¹ t` at
`π⁻¹ z`. The matrix `inclMatrix A (inr ∘ inl)` includes `X₀ ⊕ A z`, the middle block of indices, in
the whole space. -/
lemma vectorOfLastEntry_eq_mulVec (x : 𝔰.κ → A) :
    vectorOfLastEntry π t x =
      inclMatrix A (inr ∘ inl : 𝔰.MiddleIndex → 𝔰.BesselIndex) *ᵥ middleBasisMatrix 𝔰 π *ᵥ
        (x ⊕ᵥ fun _ : Unit ↦ (-(star π)⁻¹ : Aˣ) * t) := by
  -- One case for each kind of index: the `e_a`, the basis of `X₀`, the vector `z`, the `e*_a`.
  ext (a | (k | ⟨⟩) | a)
  · simp [vectorOfLastEntry, besselLatticeBasis, inclMatrix, mulVec, dotProduct, one_apply]
  · simp [middleBasisMatrix, vectorOfLastEntry, besselLatticeBasis, inclMatrix, mulVec, dotProduct,
    one_apply]
  · simp [middleBasisMatrix, vectorOfLastEntry, besselLatticeBasis, inclMatrix, mulVec, dotProduct,
    one_apply,
      mul_assoc, mul_left_comm]
  · simp [vectorOfLastEntry, besselLatticeBasis, inclMatrix, mulVec, dotProduct, one_apply]

end TailBasis

variable {A ι κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype ι]
  [DecidableEq ι] [Fintype κ] [DecidableEq κ] {𝔰 : Shape} {π : Aˣ} {N : A} {m : ℕ}

/-- At a finite place and in rank at least two, the fiber measures `P.normFiberMeasure κ`
disintegrate the volume of `κ → A` along the standard form `x ↦ x* x`. -/
lemma IntegralPlace.isDisintegration_normFiberMeasure (h_rank : 2 ≤ card κ) :
    P.IsDisintegration volume (1 : Matrix κ κ A) (P.normFiberMeasure κ) := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A, Bᴴ * B = planeSumGram 1 :=
    P.exists_hyperbolic_basis h_rank
  have h_exists : ∃ l : skewAdjoint A → Measure (κ → A),
      P.IsDisintegration volume (1 : Matrix κ κ A) l :=
    ⟨fun b ↦ (P.quadricMeasure 1 b).map (B *ᵥ ·), P.isDisintegration_of_hyperbolic_basis h_rank hB⟩
  unfold Place.normFiberMeasure
  exact Classical.epsilon_spec h_exists

/-- For a basis `B` of the standard form with Gram matrix `planeSumGram 1`, the fiber measure
`P.normFiberMeasure κ b` of `x ↦ x* x` is the image under `B` of the measure `P.quadricMeasure 1 b`
of the flat chart. -/
lemma IntegralPlace.normFiberMeasure_eq_map (h_rank : 2 ≤ card κ)
    {B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A} (hB : Bᴴ * B = planeSumGram 1) (b : skewAdjoint A) :
    P.normFiberMeasure κ b = (P.quadricMeasure 1 b).map (B *ᵥ ·) :=
  (P.isDisintegration_normFiberMeasure h_rank).unique
    (P.isDisintegration_of_hyperbolic_basis h_rank hB)

/-- At a finite place and in rank at least two, let the columns of `B` have Gram matrix
`planeSumGram 1` for the standard form `x ↦ x* x`: a hyperbolic pair, then orthonormal vectors. In
this basis `flatChart 1 b` sends coordinates `p = ((t, w), a)`, with `a` skew, to a point of the
quadric of norm `δ⁻¹ b` whenever `t` is a unit. The fiber measure `P.normFiberMeasure κ b` of
`x ↦ x* x` is the image under `p ↦ B (flatChart 1 b p)` of the volume in `(t, w)` times
`P.skewMeasure`, the Haar measure of the place on the skew elements. -/
lemma IntegralPlace.normFiberMeasure_eq_map_flatChart (h_rank : 2 ≤ card κ)
    {B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A} (hB : Bᴴ * B = planeSumGram 1) (b : skewAdjoint A) :
    P.normFiberMeasure κ b = (volume.prod P.skewMeasure).map
      fun p : (A × (Fin (card κ - 2) → A)) × skewAdjoint A ↦ B *ᵥ flatChart 1 b p := by
  have hB_meas : Measurable (B *ᵥ ·) := by fun_prop
  have h_chart_meas : Measurable (flatChart (1 : Matrix (Fin (card κ - 2)) _ A) b) := by fun_prop
  rw [P.normFiberMeasure_eq_map h_rank hB, quadricMeasure, Measure.map_map hB_meas h_chart_meas]
  rfl

/-- At the finite place `P`, if `κ` has at least two elements, the fiber measure
`P.normFiberMeasure κ b` of `x ↦ x* x` on `κ → A` lives on the quadric `x* x = δ⁻¹ b`, where
`δ = P.skewUnit`: almost every `x` satisfies this equation. -/
lemma IntegralPlace.ae_normFiberMeasure_dotProduct_eq (h_rank : 2 ≤ card κ) (b : skewAdjoint A) :
    ∀ᵐ x : κ → A ∂P.normFiberMeasure κ b, star x ⬝ᵥ x = (↑P.skewUnit⁻¹ : A) * b := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix κ (Fin 2 ⊕ Fin (card κ - 2)) A, Bᴴ * B = planeSumGram 1 :=
    P.exists_hyperbolic_basis h_rank
  have h_closed : IsClosed {x : κ → A | star x ⬝ᵥ x = (↑P.skewUnit⁻¹ : A) * b} :=
    isClosed_eq (by fun_prop) continuous_const
  -- The chart takes values on the quadric where the parameter `p.1.1` is a unit, so almost surely.
  have h_unit_pair : ∀ᵐ sw : A × (Fin (card κ - 2) → A), IsUnit sw.1 :=
    quasiMeasurePreserving_fst.ae P.ae_isUnit
  have h_unit : ∀ᵐ p : (A × (Fin (card κ - 2) → A)) × skewAdjoint A ∂volume.prod P.skewMeasure,
      IsUnit p.1.1 :=
    quasiMeasurePreserving_fst.ae h_unit_pair
  rw [P.normFiberMeasure_eq_map_flatChart h_rank hB,
    ae_map_iff (by fun_prop) h_closed.measurableSet]
  filter_upwards [h_unit] with p hp
  calc
    star (B *ᵥ flatChart 1 b p) ⬝ᵥ B *ᵥ flatChart 1 b p
      = star (flatChart 1 b p) ⬝ᵥ planeSumGram 1 *ᵥ flatChart 1 b p := by
        rw [← hB, ← mulVec_mulVec, ← star_mulVec_dotProduct]
    _ = (↑P.skewUnit⁻¹ : A) * b := form_flatChart conjTranspose_one hp

/-- Let `π π̄ = N`, let `X₀ = 𝔰.κ → A` have an orthonormal basis of at least two vectors and let `z`
be orthogonal to it, of norm `-N`; `latticeMiddleGram 𝔰 N` is the form of `X₀ ⊕ A z`. For almost
every `x` for the fiber measure `P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)` of `x ↦ x* x`,
which lives on the sphere `x* x = t t̄ / N - N`, the vector `vectorOfLastEntry π t x = x - N⁻¹ t z`
lies on the top quadric `lastVectorQuadric (latticeMiddleGram 𝔰 N)`, that of the vectors of norm
`-N` in `X₀ ⊕ A z`. -/
lemma IntegralPlace.ae_vectorOfLastEntry_mem_lastVectorQuadric (hN : π * star (π : A) = N)
    (h_rank : 2 ≤ card 𝔰.κ) (t : A) :
    ∀ᵐ x : 𝔰.κ → A ∂P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t),
      vectorOfLastEntry π t x ∈ lastVectorQuadric (latticeMiddleGram 𝔰 N) := by
  let J : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A := (latticeMiddleGram 𝔰 N).splitGram
  filter_upwards [P.ae_normFiberMeasure_dotProduct_eq h_rank (lastEntrySphereIndex π t)] with x hx
  have h_vanish (i : 𝔰.BesselIndex) (hi : floorOf i < 𝔰.ϱ) : vectorOfLastEntry π t x i = 0 := by
    -- The indices of `X₀ ⊕ A z` have floor at least `𝔰.ϱ`.
    have h_ne (a : 𝔰.MiddleIndex) : i ≠ inr (inl a) := by
      rintro rfl
      cases a <;> simp [floorOf] at hi
    simp [vectorOfLastEntry_eq_mulVec, inclMatrix, mulVec, dotProduct, one_apply, h_ne]
  have h_sphere : star x ⬝ᵥ x = ↑(π * star π)⁻¹ * t * star t - N := by
    rw [hx, ← hN]
    simp [lastEntrySphereIndex]
  obtain ⟨h_form, -⟩ : star (vectorOfLastEntry π t x) ⬝ᵥ J *ᵥ vectorOfLastEntry π t x =
      star x ⬝ᵥ x - ↑(π * star π)⁻¹ * t * star t ∧ (J *ᵥ vectorOfLastEntry π t x) 𝔰.z = t :=
    form_vectorOfLastEntry hN
  have h_norm : star (vectorOfLastEntry π t x) ⬝ᵥ J *ᵥ vectorOfLastEntry π t x = J 𝔰.z 𝔰.z :=
    calc
      _ = star x ⬝ᵥ x - ↑(π * star π)⁻¹ * t * star t := h_form
      _ = -N := by rw [h_sphere, sub_sub_cancel_left]
      _ = J 𝔰.z 𝔰.z := by simp [J, splitGram, latticeMiddleGram]
  exact ⟨h_vanish, h_norm⟩

/-- Let `E` be a basis of `X₀ ⊕ A z` that begins with a hyperbolic pair: its Gram matrix for `T` is
`planeSumGram S`, with `S` hermitian and `S * S = 1`. Then the flat chart of `E`, included in the
whole space by the matrix `inclMatrix A (inr ∘ inl)`, carries the product of the volume and of
`P.skewMeasure`, the Haar measure of the skew elements, to the measure
`F.floorQuadricMeasure 𝔰.top b` of the quadric of norm `δ⁻¹ b` in `X₀ ⊕ A z`, `δ = P.skewUnit`.
Here `F` is any basis of `X₀ ⊕ A z` made of `m + 1` hyperbolic pairs and orthonormal vectors
indexed by `ι`, and `T.splitGram`, the form of the whole space, is hermitian and invertible. -/
lemma HyperbolicBasis.measurePreserving_inclMatrix_flatChart {T : 𝔰.Form A}
    [IsHermitianUnit T.splitGram] (F : HyperbolicBasis ι T m) {S : Matrix κ κ A}
    {E : Matrix 𝔰.MiddleIndex (Fin 2 ⊕ κ) A} (hE : Eᴴ * T * E = planeSumGram S)
    (h_card : card 𝔰.MiddleIndex = card (Fin 2 ⊕ κ)) (hS : Sᴴ = S) (hS_sq : S * S = 1)
    (b : skewAdjoint A) :
    MeasurePreserving
      (fun p : (A × (κ → A)) × skewAdjoint A ↦ inclMatrix A (inr ∘ inl) *ᵥ E *ᵥ flatChart S b p)
      (volume.prod P.skewMeasure) (F.floorQuadricMeasure 𝔰.top b) := by
  -- Both families of measures disintegrate the volume of `X₀ ⊕ A z`, so they agree.
  let ι₀ : Matrix 𝔰.BesselIndex 𝔰.MiddleIndex A := inclMatrix A (inr ∘ inl)
  have h_form : ι₀ᴴ * T.splitGram * ι₀ = T := gram_inclMatrix (inr ∘ inl) T.splitGram
  have h_left : ι₀ᴴ * ι₀ = 1 := by
    simpa [ι₀, ← ext_iff, one_apply] using
      gram_inclMatrix (inr ∘ inl) (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex A)
  have h_chart : P.IsDisintegration (volume.map (ι₀ *ᵥ ·)) T.splitGram
      fun b' : skewAdjoint A ↦ ((P.quadricMeasure S b').map (E *ᵥ ·)).map (ι₀ *ᵥ ·) :=
    (isDisintegration_map_quadricMeasure hE h_card F.modulus_det hS hS_sq).map h_form h_left
  have h_vol : volume.map (ι₀ *ᵥ ·) = floorVolume 𝔰.top :=
    map_inclMatrix_eq_floorVolume (inr ∘ inl)
  have h_floor : P.IsDisintegration (volume.map (ι₀ *ᵥ ·)) T.splitGram
      fun b' : skewAdjoint A ↦ F.floorQuadricMeasure 𝔰.top b' :=
    F.isDisintegration_floorVolume 𝔰.top h_vol
  have h_chart_meas : Measurable (flatChart S b) := by fun_prop
  have h_pres : MeasurePreserving (flatChart S b) (volume.prod P.skewMeasure)
      (P.quadricMeasure S b) :=
    h_chart_meas.measurePreserving _
  have hE_meas : Measurable (E *ᵥ ·) := by fun_prop
  have hι_meas : Measurable (ι₀ *ᵥ ·) := by fun_prop
  rw [h_floor.unique h_chart]
  exact (hι_meas.measurePreserving _).comp ((hE_meas.measurePreserving _).comp h_pres)

/-- Let `π π̄ = N` and `b = -δ N`, where `δ = P.skewUnit`. The form `fromBlocks 1 0 0 (-1)` is an
orthonormal part on `κ` plus a vector of norm `-1`, and its `flatChart` parametrises the quadric of
norm `δ⁻¹ b = -N` of a hyperbolic plane plus this form. At `((s, w ⊕ -π̄⁻¹ t), a)`, this chart,
reindexed by `Equiv.sumAssoc`, equals `flatChart 1 (lastEntrySphereIndex π t) ((s, w), a)`, the
chart of the sphere of norm `t t̄ / N - N`, followed by the last coordinate `-π̄⁻¹ t`. -/
lemma flatChart_comp_sumAssoc (hN : π * star (π : A) = N) {b : skewAdjoint A}
    (hb : (b : A) = P.skewUnit * -N) (t s : A) (w : κ → A) (a : skewAdjoint A) :
    flatChart (fromBlocks 1 0 0 (-1)) b ((s, w ⊕ᵥ fun _ : Unit ↦ (-(star π)⁻¹ : Aˣ) * t), a) ∘
        Equiv.sumAssoc (Fin 2) κ Unit =
      flatChart 1 (lastEntrySphereIndex π t) ((s, w), a) ⊕ᵥ fun _ : Unit ↦
        (-(star π)⁻¹ : Aˣ) * t := by
  set u : Aˣ := -(star π)⁻¹
  let v : κ ⊕ Unit → A := w ⊕ᵥ fun _ : Unit ↦ u * t
  let S : Matrix (κ ⊕ Unit) (κ ⊕ Unit) A := fromBlocks 1 0 0 (-1)
  have h_form : star v ⬝ᵥ S *ᵥ v = star w ⬝ᵥ w - ↑(π * star π)⁻¹ * t * star t :=
    calc
      star v ⬝ᵥ S *ᵥ v = star w ⬝ᵥ w - star (u * t) * (u * t) := by
        simp [v, S, fromBlocks_mulVec, neg_mulVec, dotProduct, sub_eq_add_neg]
      _ = star w ⬝ᵥ w - ↑(π * star π)⁻¹ * t * star t := by
        simp [u, mul_comm, mul_left_comm, mul_assoc]
  -- The two charts solve for the coordinate along the first vector from the same remaining norm.
  have h_norm : (↑P.skewUnit⁻¹ : A) * b - star v ⬝ᵥ S *ᵥ v =
      (↑P.skewUnit⁻¹ : A) * lastEntrySphereIndex π t - star w ⬝ᵥ w := by
    simp only [h_form, hb, lastEntrySphereIndex, skewUnitMul_coe, Units.inv_mul_cancel_left, hN]
    ring
  simp [flatChart, v, S, h_norm, funext_iff]

/-- Let `π π̄ = N`, let `X₀` have rank at least two and let `B` be a basis of `X₀` with Gram matrix
`planeSumGram 1`. Send a pair `(t, p)` to the vector `vectorOfLastEntry π t x = x - N⁻¹ t z`, where
`x` is the point with coordinates `p` in the flat chart of the sphere `x* x = t t̄ / N - N`. This
map carries `(modulus π)⁻¹ dt` times the measure of the chart to `F.floorQuadricMeasure 𝔰.top`, the
measure, defined by a hyperbolic basis `F` of `X₀ ⊕ A z`, of the quadric of vectors of norm
`⟨z, z⟩ = -N`. -/
lemma HyperbolicBasis.measurePreserving_vectorOfLastEntry_flatChart
    [IsHermitianUnit (latticeMiddleGram 𝔰 N).splitGram]
    (F : HyperbolicBasis ι (latticeMiddleGram 𝔰 N) m)
    (hN : π * star (π : A) = N) (h_rank : 2 ≤ card 𝔰.κ)
    {B : Matrix 𝔰.κ (Fin 2 ⊕ Fin (card 𝔰.κ - 2)) A} (hB : Bᴴ * B = planeSumGram 1) :
    MeasurePreserving
      (fun p : A × (A × (Fin (card 𝔰.κ - 2) → A)) × skewAdjoint A ↦
        vectorOfLastEntry π p.1 (B *ᵥ flatChart 1 (lastEntrySphereIndex π p.1) p.2))
      (((P.modulus π)⁻¹ • volume).prod (volume.prod P.skewMeasure))
        (F.floorQuadricMeasure 𝔰.top) := by
  -- The basis `B` of `X₀` and the vector `π⁻¹ z` of norm `-1` form a basis of `X₀ ⊕ A z` that
  -- begins with a hyperbolic pair, so its flat chart gives the quadric measure.
  let extendB : Matrix (𝔰.κ ⊕ Unit) ((Fin 2 ⊕ Fin (card 𝔰.κ - 2)) ⊕ Unit) A := B.fromBlocks 0 0 1
  let fullBasis : Matrix 𝔰.MiddleIndex ((Fin 2 ⊕ Fin (card 𝔰.κ - 2)) ⊕ Unit) A :=
    middleBasisMatrix 𝔰 π * extendB
  have gram_fullBasis : fullBasisᴴ * latticeMiddleGram 𝔰 N * fullBasis =
      fromBlocks (planeSumGram 1) 0 0 (-1) := by
    rw [gram_mul, gram_middleBasisMatrix hN]
    simp [extendB, fromBlocks_conjTranspose, fromBlocks_multiply, hB]
  -- Regroup the indices as the hyperbolic pair and the rest, whose Gram matrix is `restGram`.
  let regroup : (Fin 2 ⊕ Fin (card 𝔰.κ - 2)) ⊕ Unit ≃ Fin 2 ⊕ Fin (card 𝔰.κ - 2) ⊕ Unit :=
    Equiv.sumAssoc (Fin 2) (Fin (card 𝔰.κ - 2)) Unit
  let chartBasis : Matrix 𝔰.MiddleIndex (Fin 2 ⊕ Fin (card 𝔰.κ - 2) ⊕ Unit) A :=
    fullBasis.submatrix id regroup.symm
  let restGram : Matrix (Fin (card 𝔰.κ - 2) ⊕ Unit) (Fin (card 𝔰.κ - 2) ⊕ Unit) A :=
    fromBlocks 1 0 0 (-1)
  have gram_chartBasis :
      chartBasisᴴ * latticeMiddleGram 𝔰 N * chartBasis = planeSumGram restGram :=
    calc
      _ = (fullBasisᴴ * latticeMiddleGram 𝔰 N * fullBasis).submatrix regroup.symm regroup.symm :=
        rfl
      _ = planeSumGram restGram := by simp [gram_fullBasis, restGram, regroup, ← ext_iff, one_apply]
  have restGram_herm : restGramᴴ = restGram := by simp [restGram, fromBlocks_conjTranspose]
  have restGram_sq : restGram * restGram = 1 := by simp [restGram, fromBlocks_multiply]
  have h_card : card 𝔰.MiddleIndex = card (Fin 2 ⊕ Fin (card 𝔰.κ - 2) ⊕ Unit) := by
    simp only [card_sum, card_fin, card_unique]
    omega
  have hN_star : star (-N) = -N := by simp [← hN, mul_comm]
  let level : skewAdjoint A := P.skewUnitMul (-N) hN_star
  -- The default index of the quadric measure is `δ ⟨z, z⟩`, and `⟨z, z⟩ = -N`.
  have norm_z : (latticeMiddleGram 𝔰 N).splitGram (𝔰.besselFrame 𝔰.top) (𝔰.besselFrame 𝔰.top) =
      -N := by
    simp [splitGram, latticeMiddleGram]
  have h_level : F.floorQuadricMeasure 𝔰.top = F.floorQuadricMeasure 𝔰.top level := by
    simp only [level, norm_z]
  have h_chart : MeasurePreserving
      (fun p : (A × (Fin (card 𝔰.κ - 2) ⊕ Unit → A)) × skewAdjoint A ↦
        inclMatrix A (inr ∘ inl) *ᵥ chartBasis *ᵥ flatChart restGram level p)
      (volume.prod P.skewMeasure) (F.floorQuadricMeasure 𝔰.top) := by
    rw [h_level]
    exact F.measurePreserving_inclMatrix_flatChart gram_chartBasis h_card restGram_herm
      restGram_sq level
  -- The last coordinate of this chart is `-π̄⁻¹ t`; the others are those of the sphere's chart.
  let scale : Aˣ := -(star π)⁻¹
  have modulus_scale : P.modulus scale = (P.modulus π)⁻¹ :=
    calc
      P.modulus scale = P.modulus ((star π)⁻¹ : Aˣ) := by
        rw [Units.val_neg, (P.modulus_star_and_neg _).2]
      _ = (P.modulus (star (π : A)))⁻¹ := by rw [modulus_inv, Units.coe_star]
      _ = (P.modulus π)⁻¹ := by rw [(P.modulus_star_and_neg _).1]
  have chart_eq_tailVector (t s : A) (w : Fin (card 𝔰.κ - 2) → A) (a : skewAdjoint A) :
      inclMatrix A (inr ∘ inl) *ᵥ chartBasis *ᵥ
          flatChart restGram level ((s, w ⊕ᵥ fun _ : Unit ↦ scale * t), a) =
        vectorOfLastEntry π t (B *ᵥ flatChart 1 (lastEntrySphereIndex π t) ((s, w), a)) := by
    have h_coord : chartBasis *ᵥ flatChart restGram level ((s, w ⊕ᵥ fun _ : Unit ↦ scale * t), a) =
        fullBasis *ᵥ (flatChart 1 (lastEntrySphereIndex π t) ((s, w), a) ⊕ᵥ fun _ : Unit ↦
          scale * t) := by
      rw [submatrix_mulVec_equiv, Equiv.symm_symm, flatChart_comp_sumAssoc hN rfl, comp_id]
    rw [h_coord, vectorOfLastEntry_eq_mulVec, ← mulVec_mulVec]
    simp [extendB, scale, fromBlocks_mulVec]
  rw [← modulus_scale]
  exact (h_chart.comp (measurePreserving_append_last P.skewMeasure scale)).congr (by fun_prop)
    (.of_forall fun ⟨t, ⟨s, w⟩, a⟩ ↦ chart_eq_tailVector t s w a)

/-- Let `A` be a semilocal field with involution, `P` a finite place on it and `π` a unit of `A`
with `π π̄ = N`; multiplication by `π` scales the volume of `A` by `P.modulus π`. The matrix
`latticeMiddleGram 𝔰 N` is the form of `X₀ ⊕ A z` in the lattice basis, where `X₀ = (𝔰.κ → A)` is
the standard hermitian space, of rank at least two, and `z` is orthogonal to it of norm `-N`. The
whole space `𝔰.BesselIndex → A` adds `𝔰.ϱ` hyperbolic planes, and its form is hermitian and
invertible. Let `f` be continuous of compact support on the whole space.
For `t` in `A`, take `(P.modulus π)⁻¹` times the integral of
`f (vectorOfLastEntry π t x) = f (x - N⁻¹ t z)` against the fiber measure
`P.normFiberMeasure 𝔰.κ (lastEntrySphereIndex π t)` of the sphere `x* x = t t̄ / N - N` in `X₀`.
This function of `t` is integrable, and its integral is that of `f` against
`F.floorQuadricMeasure 𝔰.top`. The latter has its default index `δ ⟨z, z⟩`, where `δ = P.skewUnit`:
it is the measure on the quadric of vectors of norm `-N` in `X₀ ⊕ A z` defined by a basis `F` made
of `m + 1` hyperbolic pairs and orthonormal vectors indexed by `ι`. -/
theorem HyperbolicBasis.integral_floorQuadricMeasure_top
    [IsHermitianUnit (latticeMiddleGram 𝔰 N).splitGram]
    (F : HyperbolicBasis ι (latticeMiddleGram 𝔰 N) m) (hN : π * star (π : A) = N)
    (h_rank : 2 ≤ card 𝔰.κ) {f : (𝔰.BesselIndex → A) → ℂ} (hf : Continuous f)
    (h_supp : HasCompactSupport f) :
    Integrable (fun t : A ↦ (P.modulus π)⁻¹.toReal *
        ∫ x : 𝔰.κ → A, f (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
          (lastEntrySphereIndex π t)) ∧
      ∫ t : A, (P.modulus π)⁻¹.toReal *
          ∫ x : 𝔰.κ → A, f (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
            (lastEntrySphereIndex π t) =
        ∫ e : 𝔰.BesselIndex → A, f e ∂F.floorQuadricMeasure 𝔰.top := by
  obtain ⟨B, hB⟩ : ∃ B : Matrix 𝔰.κ (Fin 2 ⊕ Fin (card 𝔰.κ - 2)) A, Bᴴ * B = planeSumGram 1 :=
    P.exists_hyperbolic_basis h_rank
  let K (p : A × (A × (Fin (card 𝔰.κ - 2) → A)) × skewAdjoint A) : 𝔰.BesselIndex → A :=
    vectorOfLastEntry π p.1 (B *ᵥ flatChart 1 (lastEntrySphereIndex π p.1) p.2)
  have h_pres : MeasurePreserving K (((P.modulus π)⁻¹ • volume).prod (volume.prod P.skewMeasure))
      (F.floorQuadricMeasure 𝔰.top) := F.measurePreserving_vectorOfLastEntry_flatChart hN h_rank hB
  have : IsFiniteMeasureOnCompacts (F.floorQuadricMeasure 𝔰.top) :=
    (F.isDisintegration_floorVolume 𝔰.top rfl).isFiniteMeasureOnCompacts _
  have h_int : Integrable (fun p ↦ f (K p))
      (((P.modulus π)⁻¹ • volume).prod (volume.prod P.skewMeasure)) :=
    h_pres.integrable_comp_of_integrable (hf.integrable_of_hasCompactSupport h_supp)
  -- Fubini in the coordinates `(t, p)`; the inner integral is the one over the sphere.
  let G (t : A) : ℂ := ∫ p, f (K (t, p)) ∂volume.prod P.skewMeasure
  have h_sphere (t : A) : ∫ x, f (vectorOfLastEntry π t x) ∂P.normFiberMeasure 𝔰.κ
    (lastEntrySphereIndex π t) = G t := by
    have h_chart_meas : AEMeasurable (fun p ↦ B *ᵥ flatChart 1 (lastEntrySphereIndex π t) p)
        (volume.prod P.skewMeasure) := by fun_prop
    rw [P.normFiberMeasure_eq_map_flatChart h_rank hB]
    exact integral_map h_chart_meas (by fun_prop)
  have G_int : Integrable G := by
    have h_smul : Integrable G ((P.modulus π)⁻¹ • volume) := h_int.integral_prod_left
    have h_ne_zero : (P.modulus π)⁻¹ ≠ 0 := by simp
    have h_ne_top : (P.modulus π)⁻¹ ≠ ∞ := by simp
    exact (integrable_smul_measure h_ne_zero h_ne_top).1 h_smul
  simp only [h_sphere]
  refine ⟨G_int.const_mul _, ?_⟩
  calc
    ∫ t, (P.modulus π)⁻¹.toReal * G t = ∫ t, G t ∂(P.modulus π)⁻¹ • volume := by
      rw [integral_const_mul, integral_smul_measure, Complex.real_smul]
    _ = ∫ p, f (K p) ∂((P.modulus π)⁻¹ • volume).prod (volume.prod P.skewMeasure) :=
      (integral_prod _ h_int).symm
    _ = ∫ e, f e ∂F.floorQuadricMeasure 𝔰.top := by
      rw [← h_pres.map_eq, integral_map h_pres.aemeasurable hf.aestronglyMeasurable]

end New.Floors

end
