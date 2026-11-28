import Lib.DiscreteSeries.Bruhat.FloorMeasures
import Lib.SiegelWeil.Mass

/-!
# Local measure bounds and local densities at a finite place

Local measure estimates at a finite place, and Fourier inversion for local densities near a
hermitian quadric. A finite place `New.Floors.IntegralPlace A` is a place `New.Floors.Place A` (a
ring with involution, Haar measure, modulus `modulus`, character `ψ`, an element `τ` with
`τ + star τ = 1`, a skew unit δ = `skewUnit` and a Haar measure ν = `skewMeasure` on the skew
elements) with a compact open ring of integers `R` of volume `1`.

## Main definitions and results

* `New.Floors.IntegralPlace.exists_content`, `New.Floors.IntegralPlace.contentIndex`: the content of
  a vector with a unit entry, and its index.
* `New.Floors.IntegralPlace.lintegral_contentIndex_pow_le`: if `New.idealZeta integers μ ≤ 2` and
  the dimension is large enough, the integral of a power of the index of a block of coordinates over
  the vectors v with βv integral is at most `New.idealZeta integers μ` times a power of
  `(modulus β)⁻¹`.
* `New.Floors.IntegralPlace.topEichler`, `New.Floors.IntegralPlace.orbitPoint_topEichler`: an
  explicit isometry `g` of `T.splitGram` with `FloorGroups.orbitPoint 𝔰.top g` (that is `g⁻¹ z` for
  the last frame vector `z`) equal to `e`. With `l` the index of `z`, it is built from a vector `u`
  such that h(u, y) = `y l` for all `y` and `u l = 0`. The equation holds if h(e, e) = h(z, z) and
  `e l` is a unit.
* `New.Floors.IntegralPlace.ascConv_mconv_unfolding`: the mass of a coset of the congruence subgroup
  `New.unitaryLevel`.
* `New.Floors.IntegralPlace.setIntegral_eq_slab`,
  `New.Floors.Place.IsDisintegration.setLIntegral_slab`: orthogonality of characters reduces the cut
  double integral to the mass of a slab, and that mass is an integral of masses of quadrics.
* `New.Floors.IntegralPlace.integral_skewMeasure_eq_toReal_lintegral`,
  `New.Floors.IntegralPlace.enorm_localDensity_le`: let `f ≥ 0` be continuous of compact support.
  Let `J` be hermitian, let the measures `l b` on the quadrics disintegrate Haar measure along
  `x ↦ x* J x` (`New.Floors.Place.IsDisintegration`), and let `ψ` be trivial on traces. If the outer
  integral converges absolutely, the local density of `f` at `δ⁻¹ t` is the integral of `f` against
  `l t`. Its norm is always at most this integral.

Notions from other files:
* `New.Shape.Form.splitGram`: The Gram matrix of ϱ hyperbolic planes and a middle space with Gram
  matrix T: identity blocks pair the first and last ϱ indices, T is the middle block, all else is
  zero.
* `New.idealZeta`: The ideal zeta sum ∑ [R : I]^(−s) over the ideals I of finite index in R, for a
  natural number s, with values in [0, ∞].
* `New.Shape.BesselIndex`: The index set of the basis e₁, …, e_ϱ, x_i (i in κ), z, e*₁, …, e*_ϱ.

## Relation to the literature

Known; see `Lib.SiegelWeil.OneVector.SiegelClassSum`, `Lib.Adelic.Adeles.Basic` and
`Lib.Adelic.Witt.IwasawaDecomposition` for sources.
-/

namespace New.Floors

open Matrix MeasureTheory Measure ENNReal Sum Ring Fintype FloorGroups Place Set Function
  SemilocalField

section Local

variable (A : Type) [SemilocalField A] [StarRing A]

/-- A finite place: a place `A` with its ring of integers `integers`, the subring `O` of the
semilocal field `A`. The subring `integers` is open and compact of volume `1`, is stable under
conjugation and locally a valuation ring (`New.IsAdelic`), and is self-dual for the character `ψ`.
The data of the place are normalised to `integers`: the element `element` of trace `1` is integral,
`skewUnit` is a unit of `integers`, the Plancherel constant `kernelBound` is `1`, and the skew
elements of `integers` have `skewMeasure` `1`. The modulus `modulus x` is the inverse of the
generalised index of `x integers` in `integers`. -/
class IntegralPlace extends Place A, isAdelic : IsAdelic (A := A) O where
  /-- The element `element` of trace `1` is integral. -/
  element_mem : element ∈ O
  /-- The skew unit is integral. -/
  skewUnit_mem : skewUnit.val ∈ O
  /-- The inverse of the skew unit is integral. -/
  skewUnit_inv_mem : skewUnit⁻¹.val ∈ O
  /-- The bound in the Plancherel kernel is `1`. -/
  kernelBound_eq_one : kernelBound = 1
  /-- The integral skew elements have measure `1`. -/
  skewMeasure_setOf_mem : skewMeasure {b : skewAdjoint A | b.val ∈ O} = 1
  /-- The ring of integers `R = O` is self-dual for `ψ`: the character `r ↦ ψ (r * a)` is trivial on
  `R` if and only if `a ∈ R`. -/
  self_dual (a : A) : (∀ r ∈ O, ψ (r * a) = 1) ↔ a ∈ O
  /-- The modulus `modulus x` is the inverse of the generalised index of `x integers` in
  `integers`. -/
  modulus_eq_inv_genIndex (x : A) : modulus x = (ENNReal.ofReal (genIndex x))⁻¹

variable {A}

namespace IntegralPlace

/-- The ring of integers of the finite place: the compact open subring O of A. -/
abbrev integers [IntegralPlace A] : Subring A := O

variable [P : IntegralPlace A]

/-- The data of a finite place are normalised to its ring of integers: `element`, `skewUnit` and its
inverse are integral, `kernelBound` is `1`, and the integral skew elements have measure `1`. -/
theorem data_normalised :
    P.element ∈ O ∧
    P.skewUnit.val ∈ O ∧
    P.skewUnit⁻¹.val ∈ O ∧
    P.kernelBound = 1 ∧
    P.skewMeasure {b : skewAdjoint A | b.val ∈ O} = 1 :=
  ⟨element_mem, skewUnit_mem, skewUnit_inv_mem, kernelBound_eq_one, skewMeasure_setOf_mem⟩

/-! ### Volumes of fractional ideals and lattices -/

/-- For a unit `u` of `A`, the set `u⁻¹ R` has volume `(modulus u)⁻¹`, where `R` is the ring of
integers (the subring `O`) and `modulus` the modulus of the place `P`. -/
@[simp]
theorem volume_setOf_mul_mem (u : Aˣ) : volume {x : A | u.val * x ∈ integers} =
  (P.modulus u)⁻¹ := by
  calc volume {x : A | u.val * x ∈ integers} = Measure.map (u.val * ·) volume
         (P.integers : Set A) :=
        (map_apply (measurable_const_mul u.1) isCompact_O.measurableSet).symm
    _ = (P.modulus u)⁻¹ := by simp [P.map_mul_volume, volume_O]

/-- For a unit `c` of `A` that lies in `R`, the set `c R` is an ideal of `R` of finite index
`(modulus c)⁻¹`. -/
theorem exists_ideal_cardQuot_eq (c : Aˣ) (hc_mem : ↑c ∈ P.integers) :
    ∃ I : Ideal P.integers,
      I.cardQuot ≠ 0 ∧
      integers.subtype '' I = {x : A | c⁻¹.val * x ∈ integers} ∧
      I.cardQuot = (P.modulus c)⁻¹ := by
  -- Take `I = c R`. Its index is `genIndex c`, which is not zero and equals `(P.modulus c)⁻¹`.
  have h_index : (Submodule.cardQuot (Ideal.span {(⟨c, hc_mem⟩ : P.integers)}) : ℝ) = genIndex
    c.1 := by
    simp [genIndex_eq_card isOpen_O, Submodule.cardQuot_apply, hc_mem, isCompact_O]
  refine ⟨.span {⟨c, hc_mem⟩}, mod_cast h_index.trans_ne (genIndex_pos c).ne', ?_, ?_⟩
  · simp [Set.ext_iff, ← range_comp, Submodule.span_singleton_eq_range, ← c.eq_mul_inv_iff_mul_eq,
      mul_comm]
  · rw [modulus_eq_inv_genIndex, inv_inv, ← h_index, ofReal_natCast]

/-- For a self-adjoint unit `u`, the skew elements of `u⁻¹ O` have measure
`modulus u ^ (-1 / 2)`. -/
lemma skewMeasure_setOf_mul_mem (u : Aˣ) (h : star u.val = u) :
    P.skewMeasure {b : skewAdjoint A | u * b.val ∈ integers} = (P.modulus u ^ (2⁻¹ : ℝ))⁻¹ := by
  -- Evaluate `map_skewMeasure_mul_unit` on the integral skew elements, which have measure 1. As
  -- `element + star element = 1`, `star u = u` and `b` is skew, `skewPart` sends `element * u * b`
  -- to `u * b`.
  have h_scale : P.skewMeasure ((fun b ↦ skewPart (P.element * u * b.1)) ⁻¹' {b | b.1 ∈ P.integers})
    =
      ((P.modulus u ^ (2⁻¹ : ℝ))⁻¹ • P.skewMeasure) {b | b.1 ∈ P.integers} := by
    rw [← map_skewMeasure_mul_unit u h]
    exact (map_apply (by fun_prop) isOpen_O.preimage_val.measurableSet).symm
  have h_part (b : skewAdjoint A) : P.element * u * b.1 - star (P.element * u * b.1) = u * b.1 := by
    simp [h, ← add_mul, skewAdjoint.star_val_eq]
  simpa only [preimage, mem_ofPred_eq, SetLike.mem_coe, h_part, Measure.smul_apply,
    skewMeasure_setOf_mem, smul_eq_mul, mul_one] using h_scale

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
/-- The lattice of integral vectors is open and compact, of volume `1`. -/
theorem isOpen_isCompact_volume_intVectors :
    let L : Set (ι → A) := intVectors P.integers ι
    IsOpen L ∧ IsCompact L ∧ volume L = 1 := by
  have h_eq : (intVectors P.integers ι : Set (ι → A)) = univ.pi fun _ : ι ↦
    (P.integers : Set A) := by
    simp [Set.ext_iff, intVectors]
  refine ⟨isOpen_intVectors isOpen_O, ?_, by simp [h_eq, volume_pi_pi, volume_O]⟩
  simpa [h_eq] using isCompact_univ_pi fun _ : ι ↦ isCompact_O

/-- A set that contains `u R` has volume at least `modulus u`. -/
theorem modulus_le_volume {u : Aˣ} {S : Set A} (h_mul_mem : ∀ r ∈ P.integers, u * r ∈ S) :
    P.modulus u ≤ volume S := by
  calc P.modulus u = volume {x | u⁻¹.1 * x ∈ P.integers} := by simp [modulus_inv]
    _ ≤ volume S := measure_mono fun x hx ↦ by simpa using h_mul_mem _ hx

/-- A unit of `A` that lies in `R` has modulus at most `1`. -/
theorem modulus_le_one (u : Aˣ) (hu_mem : u.val ∈ integers) : P.modulus u ≤ 1 := by
  simp [modulus_eq_inv_genIndex, one_le_genIndex hu_mem]

/-- The principal congruence subgroups `unitaryLevel integers g J` (the `k` with `k`, `k⁻¹` and
`g⁻¹ (k - 1)` integral) of the unitary group `U J` of the matrix `J` are open for every unit `g`,
and the one of level `1` is compact. -/
theorem unitaryLevel_open_compact {J : Matrix ι ι A} :
    (∀ {g : Aˣ}, (unitaryLevel integers g J).IsOpen) ∧ IsCompact
      (unitaryLevel integers 1 J : Set (U J)) := by
  -- Both conditions, `k ∈ GL(integers)` and `g⁻¹ • (k - 1)` integral, are open because `integers`
  -- is.
  refine ⟨(isOpen_intGL isOpen_O).preimage_val.and isOpen_O.matrix.preimage_of_continuous, ?_⟩
  -- At level 1 the group is the trace of the compact `GL(O)` on the closed subgroup `U J`.
  rw [unitaryLevel_one]
  exact (isCompact_intGL isCompact_O).preimage_val (isClosed_U J)

/-- The determinant of a matrix in `GL(R)` has modulus `1`. -/
theorem modulus_det_eq_one {V : GL ι A} (hV : V ∈ intGL ι P.integers) : modulus V.val.det = 1 := by
  simp [modulus_eq_inv_genIndex, genIndex_det_eq_one isOpen_O, hV, isCompact_O]

/-! ### The content of a vector -/

/-- Content: if some entry of `p` is a unit of `A`, there are a unit `t` of `A` and a row `r` over
`integers` with `r ⬝ᵥ p = t` such that `c • p` is integral exactly when `t * c ∈ integers`. -/
theorem exists_content {p : ι → A} {i : ι} (h_unit : IsUnit (p i)) :
    ∃ t : Aˣ, ∃ r ∈ intVectors integers ι,
      r ⬝ᵥ p = t ∧
      ∀ c : A, (∀ j : ι, c * p j ∈ integers) ↔ t * c ∈ integers := by
  -- Hermite form of the column `p`: there is `V` in `GL(O)` such that `p` is a scalar times column
  -- `i` of `V`, the scalar being the product of row `i` of `V⁻¹` with `p`.
  obtain ⟨V, (hV : V ∈ intGL ι P.integers), _, -,
      (h_column : replicateCol Unit p = V.val.submatrix id (Embedding.punit i) * _), rfl⟩ :=
    P.isAdelic.isValuationPair.hermite (.punit i) (replicateCol Unit p)
  have h_col (j : ι) : p j = V.1 j i * V⁻¹.1 i ⬝ᵥ p := by
    simpa [mul_apply, dotProduct, Embedding.punit, -coe_units_inv] using congrFun₂ h_column j ()
  -- The scalar divides the unit `p i`, so it is a unit `t`.
  have h_prod_unit : IsUnit (V.1 i i * V⁻¹.1 i ⬝ᵥ p) := by rwa [← h_col i]
  obtain ⟨t, ht⟩ : IsUnit (V⁻¹.1 i ⬝ᵥ p) := isUnit_of_mul_isUnit_right h_prod_unit
  refine ⟨t, V⁻¹.1 i, hV.isIntMatrix_inv i, ht.symm, fun c ↦ ⟨fun hc ↦ ?_, fun hc j ↦ ?_⟩⟩
  · have h_apply : (V⁻¹.1 *ᵥ c • p) i = t * c := by
      simp [mulVec, ht, mul_comm c, -coe_units_inv]
    rw [← h_apply]
    exact hV.isIntMatrix_inv.mulVec (v := c • p) hc i
  · have h_int : V.1 j i * (t * c) ∈ integers := mul_mem (hV.isIntMatrix j i) hc
    simpa [h_col j, ht, mul_comm c, mul_assoc] using h_int

/-- The volume of the set of c in A with cp integral if the entry p_i is a unit of A, and ∞
otherwise. -/
noncomputable def contentIndex (i : ι) (p : ι → A) : ℝ≥0∞ :=
  ⨅ _ : IsUnit (p i), volume {c : A | ∀ j : ι, c * p j ∈ integers}

omit [DecidableEq ι] in
/-- The content index at `i` is a measurable function of the vector. -/
@[fun_prop]
theorem measurable_contentIndex {i : ι} : Measurable (P.contentIndex i) := by
  classical
  unfold contentIndex
  simp_rw [iInf_eq_if]
  -- Where `p i` is a unit, the value is the volume of a fibre of the set of `(c, p)` with `c • p`
  -- integral; elsewhere it is constant.
  have h_units : MeasurableSet {p : ι → A | IsUnit (p i)} :=
    measurableEmbedding_units_val.measurableSet_range.preimage (by fun_prop)
  have h_integral : MeasurableSet {q : A × (ι → A) | ∀ j, q.1 * q.2 j ∈ integers} :=
    measurable_smul isOpen_isCompact_volume_intVectors.1.measurableSet
  exact .ite h_units (measurable_measure_prodMk_right h_integral) measurable_const

/-- Let ζ_O(μ) ≤ 2, V ∈ GL_ι(O), β a unit, and single out the coordinates indexed by κ of Vᴴw,
through σ. Suppose |κ| = s + k with k ≥ μ, and put d = |n| + k, so that d = |ι| − s. The integral of
the s-th power of the content index (`New.Floors.IntegralPlace.contentIndex`) of these coordinates
over the w with βw integral is at most ζ_O(μ)·md(β)^(−d), where md is the modulus, O is the ring of
integers, GL_ι(O) is `intGL ι integers` and ζ_O is `New.idealZeta integers`. -/
theorem lintegral_contentIndex_pow_le {s μ : ℕ} (hμ : idealZeta P.integers μ ≤ 2) {n : Type*}
    {k d : ℕ} [Fintype n] (σ : n ⊕ κ ≃ ι) (i : κ) {V : GL ι A} (β : Aˣ) (hV : V ∈ intGL ι integers)
    (hd : card n + k = d ∧ card κ = s + k ∧ μ ≤ k) :
    ∫⁻ w : ι → A in {w : ι → A | ∀ j : ι, β.val * w j ∈ integers},
        contentIndex i (fun j : κ ↦ (V.valᴴ *ᵥ w) (σ (inr j))) ^ s ≤
      idealZeta P.integers μ * (P.modulus β)⁻¹ ^ d := by
  classical
  -- Put `y = Vᴴ w`, a change of variables that keeps the volume. If the singled out coordinates of
  -- `y` have content `t`, those of `β y` lie in the ideal `I = t β O`. Sum over `I`: by
  -- `lintegral_le_idealZeta_mul` it is enough to bound `[O : I] ^ μ` times the integrand times the
  -- volume of the box of `I`.
  obtain ⟨rfl, (hκ_card : card κ = s + k), (hμ_le : μ ≤ k)⟩ := hd
  have h_vol : MeasurePreserving V.1ᴴ.mulVec :=
    ⟨by fun_prop, by simp [P.map_mulVec_volume, modulus_det_eq_one, hV]⟩
  let box (I : Ideal P.integers) : Set (ι → A) :=
    univ.pi fun i ↦ (β.1 * ·) ⁻¹' ite (σ.symm i).isLeft ↑P.integers (integers.subtype '' I)
  refine lintegral_le_idealZeta_mul hμ (fun I ↦ V.1ᴴ.mulVec ⁻¹' box I) ?_
  filter_upwards [h_vol.quasiMeasurePreserving.ae (tendsto_eval_ae_ae.eventually ae_isUnit)]
    with w (hw_unit : IsUnit ((V.1ᴴ *ᵥ w) (σ (inr i)))) hw_int
  obtain ⟨t, -, -, -, (ht : ∀ c : A, (∀ j : κ, c * (V.1ᴴ *ᵥ w) (σ (inr j)) ∈ integers) ↔ t * c ∈
    integers)⟩ :=
    exists_content (p := fun j ↦ (V.1ᴴ *ᵥ w) (σ (inr j))) hw_unit
  have hy_int (j : ι) : β.1 * (V.1ᴴ *ᵥ w) j ∈ P.integers := by
    simpa [mulVec_smul] using hV.isIntMatrix.conjTranspose.mulVec (v := β.1 • w) hw_int j
  obtain ⟨I, hI_ne, hI_eq, hI_card⟩ := exists_ideal_cardQuot_eq (t * β) (by simp [← ht, hy_int])
  have h_box_eq : box I = univ.pi fun j : ι ↦
      (β.1 * ·) ⁻¹' ite (σ.symm j).isLeft ↑P.integers {x : A | (t * β)⁻¹.1 * x ∈ integers} := by
    simp only [box, hI_eq]
  refine ⟨I, hI_ne, by simp [h_box_eq, reindex_equiv σ, mul_mul_mul_comm, hy_int, ht], ?_⟩
  have h_index : contentIndex i (fun j ↦ (V.1ᴴ *ᵥ w) (σ (inr j))) = (P.modulus t)⁻¹ := by
    simp only [contentIndex, iInf_pos hw_unit, ht, volume_setOf_mul_mem]
  have h_box : volume (box I) = (P.modulus β)⁻¹ ^ card n * P.modulus t ^ (s + k) := by
    simp [h_box_eq, volume_pi_pi, ← σ.prod_comp, preimage, mul_mul_mul_comm, modulus_inv, hκ_card]
  -- In the product of the indices of `I` and of the content with the volume of the box, the powers
  -- of `modulus t` cancel.
  grw [hμ_le, hI_card, h_vol.measure_preimage_le, h_box, h_index]
  · calc
      _ = ((P.modulus t)⁻¹ * (P.modulus β)⁻¹) ^ k *
          ((P.modulus t)⁻¹ ^ s * ((P.modulus β)⁻¹ ^ card n * P.modulus t ^ (s + k))) := by
        simp [ENNReal.mul_inv]
      _ = (P.modulus β)⁻¹ ^ (card n + k) * (P.modulus t * (P.modulus t)⁻¹) ^ (s + k) := by ring
      _ ≤ (P.modulus β)⁻¹ ^ (card n + k) := by grw [(P.modulus t).mul_inv_le_one, one_pow, mul_one]
  · exact_mod_cast hI_ne.pos

end IntegralPlace

end Local

namespace IntegralPlace

variable {A : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] {𝔰 : Shape}

/-! ### Eichler maps to the last frame vector -/
/-- Let `z` be the last frame vector, `l` its index, `h` the form and `v = e - z`. This is the
matrix of the scaled Eichler map `1 + u h(v, ·) - (e l)⁻¹ (v + s u) h(u, ·)` along `u`, where
`s = h(v, e) - τ (h(e, e) - h(z, z))` and `τ = P.element`. It is the identity if `e l` is not a
unit. -/
noncomputable def topEichlerMatrix (T : 𝔰.Form A) (u e : 𝔰.BesselIndex → A) :
    Matrix 𝔰.BesselIndex 𝔰.BesselIndex A :=
  let l : 𝔰.BesselIndex := 𝔰.besselFrame 𝔰.top
  let z : 𝔰.BesselIndex → A := Pi.single l 1
  let h (x y : 𝔰.BesselIndex → A) : A := star x ⬝ᵥ T.splitGram *ᵥ y
  1 + inverse (e l) • (vecMulVec (e l • u) (star (e - z) ᵥ* T.splitGram) -
    vecMulVec (e - z + (h (e - z) e - P.element * (h e e - h z z)) • u) (star u ᵥ* T.splitGram))

variable {T : 𝔰.Form A} {e : 𝔰.BesselIndex → A} [IsHermitianUnit T.splitGram]

/-- If pairing with `u` under the Gram matrix `T.splitGram` reads the coordinate at the last frame
vector `z` and this coordinate of `u` is zero, the scaled Eichler map attached to `e` along `u` is
an isometry of `T.splitGram`. -/
lemma gram_topEichlerMatrix {u : 𝔰.BesselIndex → A}
    (hu_dual : star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1)
    (hu_last : u (𝔰.besselFrame 𝔰.top) = 0) (e : 𝔰.BesselIndex → A) :
    (topEichlerMatrix T u e)ᴴ * T.splitGram * topEichlerMatrix T u e = T.splitGram := by
  have pair_left (y : 𝔰.BesselIndex → A) :
      star u ⬝ᵥ T.splitGram *ᵥ y = y (𝔰.besselFrame 𝔰.top) := by
    simp [dotProduct_mulVec, hu_dual]
  have pair_right (y : 𝔰.BesselIndex → A) :
      star y ⬝ᵥ T.splitGram *ᵥ u = star (y (𝔰.besselFrame 𝔰.top)) := by
    rw [← star_dotProduct_mulVec_comm IsHermitianUnit.conjTranspose_eq, pair_left]
  -- It is enough that `h(Mx, My) = h(x, y)` for the matrix `M` of the map, a scalar identity. If
  -- `e l` is not a unit, its inverse is `0` and `M = 1`.
  have h_isometry (x y : 𝔰.BesselIndex → A) :
      star (topEichlerMatrix T u e *ᵥ x) ⬝ᵥ T.splitGram *ᵥ (topEichlerMatrix T u e *ᵥ y) =
        star x ⬝ᵥ T.splitGram *ᵥ y := by
    -- The rules that would evaluate `T.splitGram *ᵥ z` and `star z` are switched off.
    simp [topEichlerMatrix, vecMulVec_mulVec, ← dotProduct_mulVec, ↓op_smul_eq_smul, pair_left,
      pair_right, -mulVec_single, -Pi.star_single, add_mulVec, smul_mulVec, sub_mulVec, mulVec_add,
      mulVec_sub, mulVec_smul]
    grind [star_dotProduct_mulVec_comm, IsHermitianUnit.conjTranspose_eq, inverse_non_unit,
      besselFrame_top]
  ext i j
  have h_row : (topEichlerMatrix T u e)ᴴ i = star ((topEichlerMatrix T u e).col i) := rfl
  rw [mul_mul_apply, h_row]
  simpa [col] using h_isometry (Pi.single i 1) (Pi.single j 1)

section Eichler

variable {u : 𝔰.BesselIndex → A}
  (hu_dual : star u ᵥ* T.splitGram = Pi.single (𝔰.besselFrame 𝔰.top) 1)
  (hu_last : u (𝔰.besselFrame 𝔰.top) = 0)

include hu_dual hu_last

/-- The scaled Eichler map along `u` attached to `e`, as an element of the unitary group. -/
noncomputable def topEichler (e : 𝔰.BesselIndex → A) : T.G :=
  U.of IsHermitianUnit.isUnit (topEichlerMatrix T u e) (gram_topEichlerMatrix hu_dual hu_last e)

/-- The matrix of `topEichler` is `topEichlerMatrix`. -/
lemma coe_topEichler : (topEichler hu_dual hu_last e).val.val = topEichlerMatrix T u e := rfl

/-- If the entries of `e` of floor below `𝔰.ϱ` vanish, the scaled Eichler map along `u` attached to
`e` fixes every basis vector of floor below `𝔰.ϱ`. -/
lemma topEichler_mem_floorGroup (he : ∀ i : 𝔰.BesselIndex, floorOf i < 𝔰.ϱ → e i = 0) :
    topEichler hu_dual hu_last e ∈ T.floorGroup 𝔰.ϱ := by
  -- The basis vectors of floor below `𝔰.ϱ` are orthogonal to `e - z` and to `u`, so they are fixed.
  simp +contextual [mem_floorGroup, coe_topEichler, topEichlerMatrix, hu_dual, vecMulVec_apply, he]

/-- The scaled Eichler map takes `e` to `z` if `e` has the norm of `z` and its coordinate at `z` is
a unit. -/
lemma orbitPoint_topEichler (h_norm : star e ⬝ᵥ T.splitGram *ᵥ e = T.splitGram 𝔰.z 𝔰.z)
    (h_unit : IsUnit (e (𝔰.besselFrame 𝔰.top))) :
    orbitPoint 𝔰.top (topEichler hu_dual hu_last e) = e := by
  have pair_left (y : 𝔰.BesselIndex → A) :
      star u ⬝ᵥ T.splitGram *ᵥ y = y (𝔰.besselFrame 𝔰.top) := by simp [dotProduct_mulVec, hu_dual]
  -- Put `v = e - z`. As `h(e, e) = h(z, z)`, the coefficient of `u` in the image of `e` cancels,
  -- and `e` goes to `e - v = z`.
  refine orbitPoint_eq_iff.2 ?_
  have norm_z : star (Pi.single 𝔰.z 1 : 𝔰.BesselIndex → A) ⬝ᵥ T.splitGram *ᵥ Pi.single 𝔰.z 1 =
      T.splitGram 𝔰.z 𝔰.z := by simp
  -- The rules that would evaluate `h(·, z)` (`mulVec_single`, `Pi.star_single`) are switched off.
  have h_image : topEichlerMatrix T u e *ᵥ e =
      e + inverse (e 𝔰.z) • e 𝔰.z • (Pi.single 𝔰.z 1 - e) := by
    simp [topEichlerMatrix, vecMulVec_mulVec, ← dotProduct_mulVec, ↓op_smul_eq_smul, pair_left,
      -mulVec_single, -Pi.star_single, add_mulVec, smul_mulVec, sub_mulVec, h_norm, norm_z]
    module
  simp [coe_topEichler, h_image, smul_smul, inverse_mul_cancel _ (by simpa using h_unit)]

/-- The scaled Eichler map attached to the last frame vector `z` itself is the identity. -/
lemma topEichler_single : topEichler hu_dual hu_last (Pi.single (𝔰.besselFrame 𝔰.top) 1) = 1 := by
  ext
  simp [coe_topEichler, topEichlerMatrix]

/-- The scaled Eichler map depends measurably on `e`. -/
lemma measurable_topEichler : Measurable (topEichler hu_dual hu_last) := by
  refine measurable_unitary_of_coe ?_
  simp only [coe_topEichler, topEichlerMatrix]
  fun_prop

/-- The scaled Eichler map along `u` depends continuously on `e` at every point `e` such that
inversion is continuous at its entry at the last frame vector `z`. -/
lemma continuousAt_topEichler (h_inv : ContinuousAt inverse (e (𝔰.besselFrame 𝔰.top))) :
    ContinuousAt (topEichler hu_dual hu_last) e := by
  rw [isClosedEmbedding_unitary_coe.continuousAt_iff]
  simp only [comp_def, coe_topEichler, topEichlerMatrix]
  exact continuousAt_const.add
    ((h_inv.comp_of_eq (continuousAt_apply _ e) rfl).smul (Continuous.continuousAt (by fun_prop)))

end Eichler

/-! ### Cosets of congruence subgroups -/

/-- The group of units of R, as a subset of A. -/
def intUnits : Set A := {u ∈ P.integers | ∃ v : Aˣ, v⁻¹.val ∈ integers ∧ v = u}

omit [IsHermitianUnit T.splitGram] in
lemma measurableSet_unitaryLevel {g : Aˣ} :
    MeasurableSet (unitaryLevel integers g T.splitGram : Set T.G) :=
  unitaryLevel_open_compact.1.measurableSet

omit [IsHermitianUnit T.splitGram] in
/-- For a subgroup `S`, the set `S K c⁻¹` is measurable, where `K` is the congruence subgroup of
level `g`. -/
lemma measurableSet_exists_mul_mem_level {g : Aˣ} {c : T.G} {S : Subgroup T.G} :
    MeasurableSet {y : T.G | ∃ n ∈ S, n * (y * c) ∈ unitaryLevel integers g T.splitGram} := by
  -- It is a union of translates of the open set `K`.
  rw [ofPred_exists]
  exact (isOpen_iUnion fun _ ↦
    .and (by simp) unitaryLevel_open_compact.1.preimage_of_continuous).measurableSet

/-- Unfolding at a finite place: let η be the ascending convolution `ascConv heisenbergMeasure j` of
the measures on the first `j` Heisenberg groups, K the congruence subgroup of level `g`, θ an
s-finite measure and c an element of the unitary group. Then (η∗θ)(K c⁻¹) = η(K)·θ(N K c⁻¹), with
N = `unipotentBelow j` the unipotent group on the floors below `j`. -/
theorem ascConv_mconv_unfolding {g : Aˣ} {c : T.G} {θ : Measure T.G} [SFinite θ] {j : ℕ} :
    (ascConv heisenbergMeasure j ∗ₘ θ) {y : T.G | y * c ∈ unitaryLevel integers g T.splitGram} =
      ascConv heisenbergMeasure j (SetLike.coe (unitaryLevel integers g T.splitGram)) *
        θ {y : T.G | ∃ u ∈ unipotentBelow j, u * (y *
          c) ∈ unitaryLevel integers g T.splitGram} := by
  -- Write both sides as integrals over `y` against `θ` and compare the integrands.
  have h_level : MeasurableSet {y : T.G | y * c ∈ unitaryLevel integers g T.splitGram} :=
    measurable_mul_const c measurableSet_unitaryLevel
  rw [mconv_apply_eq_lintegral h_level,
    ← lintegral_indicator_const measurableSet_exists_mul_mem_level]
  refine lintegral_congr fun y ↦ ?_
  rw [indicator]
  split_ifs with hy
  · -- The measure is invariant under right translation by `u`, and `x * u * y * c` lies in the
    -- congruence subgroup exactly when `x` does.
    obtain ⟨u, hu_mem, hu_level⟩ := hy
    have h_inv : ascConv heisenbergMeasure j ∗ₘ dirac u = ascConv heisenbergMeasure j :=
      (ascConv_heisenbergMeasure_invariant hu_mem).1
    nth_rw 1 [← h_inv, mconv_dirac]
    simp [(measurableEmbedding_mulRight u).map_apply, mul_assoc, mul_mem_cancel_right hu_level]
  · -- The measure is carried by `unipotentBelow j`, which does not meet the set in question.
    have h_notMem : ∀ x ∈ T.unipotentBelow j, x * y * c ∉ unitaryLevel integers g T.splitGram := by
      simpa [mul_assoc] using hy
    exact compl_mem_ae_iff.1 (ae_ascConv_mem_unipotentBelow.mono h_notMem)

end IntegralPlace

/-! ### Fourier inversion for local densities -/

section Inversion

open Filter Topology NNReal
variable {A κ : Type} [SemilocalField A] [StarRing A] [P : IntegralPlace A] [Fintype κ]
  {J : Matrix κ κ A} {l : skewAdjoint A → Measure (κ → A)}

/-- Duality on the skew elements. Let `u` be a hermitian unit, `y` hermitian, and `ψ` trivial on
traces. Then `b ↦ ψ (e b y)` is trivial on the skew `b` with `u b` integral if and only if `u⁻¹ δ y`
is integral, that is, lies in the ring of integers `O` of the place. Here `e = P.element`,
`e + ē = 1` and `δ = P.skewUnit`. -/
lemma IntegralPlace.psi_skew_eq_one_iff {u : Aˣ} (hu : star u.1 = u) {y : A} (hy : star y = y)
    (hψ : ∀ x : A, P.ψ (x + star x) = 1) :
    (∀ b : skewAdjoint A, u * b.1 ∈ O → P.ψ (P.element * b * y) = 1) ↔
      u⁻¹.1 * (P.skewUnit * y) ∈ O := by
  have hu' : star u⁻¹.1 = u⁻¹.1 := by simp [← Units.coe_star_inv, (Units.ext hu : star u = u)]
  set v : A := u⁻¹.1 * (P.skewUnit * y) with hv
  have v_skew : star v = -v := by simp [hv, hu', hy, P.star_skewUnit, mul_comm, mul_left_comm]
  refine ⟨fun h ↦ (P.self_dual v).1 fun r hr ↦ ?_, fun hv_int b hb ↦ ?_⟩
  · -- Take `b = u⁻¹ δ (r + r̄)`; then `r v` is `e b y` plus a trace.
    let b : skewAdjoint A := skewPart (u⁻¹.1 * (r * P.skewUnit))
    have hb : b.1 = u⁻¹.1 * ((r + star r) * P.skewUnit) := by
      simp only [b, star_mul', hu', P.star_skewUnit]
      ring
    have b_int : u * b.1 ∈ O := by
      rw [hb, u.mul_inv_cancel_left]
      exact mul_mem (add_mem hr (P.isAdelic.star_mem hr)) P.skewUnit_mem
    have h_split : r * v = P.element * b * y +
      (star P.element * r * v + star (star P.element * r * v)) := by
      rw [hb, star_mul', star_mul', star_star, v_skew, hv]
      linear_combination (-r * (u⁻¹.1 * (P.skewUnit * y))) * P.element_add_star
    rw [h_split, P.ψ.map_add_eq_mul, h b b_int, hψ, mul_one]
  · -- `e b y` is the integral element `e δ⁻¹ (u b)` times `v`.
    have h_split : P.element * b * y = P.element * P.skewUnit⁻¹.1 * (u * b.1) * v := by
      rw [hv]
      linear_combination (-P.element * b * y * (u * u⁻¹.1)) * P.skewUnit.inv_mul -
        P.element * b * y * u.mul_inv
    rw [h_split]
    exact (P.self_dual v).2 hv_int _ (mul_mem (mul_mem P.element_mem P.skewUnit_inv_mem) hb)

/-- Orthogonality of characters. Integrate `∫ f(x) ψ(e b (x* J x − α)) dx` over the skew elements
`b` with `u b` integral, with respect to `P.skewMeasure`. The result is the `P.skewMeasure`-measure
of these `b` times the mass of `f` on the slab where `u⁻¹ δ (x* J x − α)` is integral. Here `f ≥ 0`
is continuous of compact support, `J`, `u` and `α` are hermitian, `ψ` is trivial on traces,
`δ = P.skewUnit` is the skew unit of the place, `e = P.element` with `e + ē = 1`, and integral means
in the ring of integers `O` of the place. -/
lemma IntegralPlace.setIntegral_eq_slab (hJ : Jᴴ = J) (hψ : ∀ x : A, P.ψ (x + star x) = 1)
    {f : (κ → A) → ℝ≥0} (hf : Continuous f) (h_supp : HasCompactSupport f) {u : Aˣ}
    (hu : star u.1 = u) {α : A} (hα : star α = α) :
    ∫ b : skewAdjoint A in {b : skewAdjoint A | u * b.1 ∈ O},
        ∫ x : κ → A, f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - α)) ∂volume ∂P.skewMeasure =
      (P.skewMeasure {b : skewAdjoint A | u * b.1 ∈ O} *
        ∫⁻ x : κ → A in {x : κ → A | u⁻¹.1 * (P.skewUnit * (star x ⬝ᵥ J *ᵥ x - α)) ∈ O},
          f x).toReal := by
  classical
  let M : AddSubgroup (skewAdjoint A) :=
    P.integers.toAddSubgroup.comap ((AddMonoidHom.mulLeft u.1).comp (skewAdjoint A).subtype)
  have M_open : IsOpen (M : Set (skewAdjoint A)) :=
    isOpen_O.preimage (continuous_subtype_val.const_mul _)
  have coe_M : (M : Set (skewAdjoint A)) = {b : skewAdjoint A | u.1 * b.1 ∈ O} := rfl
  have M_fin : P.skewMeasure M ≠ ∞ := by simp [coe_M, P.skewMeasure_setOf_mul_mem u hu]
  have : IsFiniteMeasure (P.skewMeasure.restrict M) := isFiniteMeasure_restrict.2 M_fin
  let slab : Set (κ → A) := {x | u⁻¹.1 * (P.skewUnit * (star x ⬝ᵥ J *ᵥ x - α)) ∈ O}
  have slab_meas : MeasurableSet slab := isOpen_O.measurableSet.preimage (by fun_prop)
  have f_int : Integrable fun x ↦ (f x : ℝ) :=
    (NNReal.continuous_coe.comp hf).integrable_of_hasCompactSupport (h_supp.comp_left rfl)
  have h_int : Integrable (uncurry fun (b : skewAdjoint A) (x : κ → A) ↦
      f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - α)))
        ((P.skewMeasure.restrict M).prod volume) :=
    (f_int.comp_snd _).mono' (by fun_prop) (by simp [uncurry])
  -- For fixed `x` the character of `M` is trivial exactly on the slab.
  have inner (x : κ → A) :
      ∫ b in M, f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - α)) ∂P.skewMeasure =
      (P.skewMeasure.real M * slab.indicator (fun x ↦ (f x : ℝ)) x : ℝ) := by
    have hy : star (star x ⬝ᵥ J *ᵥ x - α) = star x ⬝ᵥ J *ᵥ x - α := by
      simp [star_dotProduct_mulVec_comm hJ, hα]
    have h_char (b b' : skewAdjoint A) :
        P.ψ (P.element * ↑(b + b') * (star x ⬝ᵥ J *ᵥ x - α)) =
          P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - α)) *
            P.ψ (P.element * b'.1 * (star x ⬝ᵥ J *ᵥ x - α)) := by
      rw [AddSubgroup.coe_add, mul_add, add_mul, P.ψ.map_add_eq_mul]
    rw [integral_const_mul, setIntegral_char M_open h_char]
    have h_triv : (∀ b ∈ M, P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - α)) = 1) ↔ x ∈ slab :=
      psi_skew_eq_one_iff hu hy hψ
    simp only [h_triv]
    by_cases hx : x ∈ slab <;> simp [hx, mul_comm (f x : ℂ)]
  calc
    _ = ∫ x, ∫ b in M, f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - α)) ∂P.skewMeasure :=
      integral_integral_swap h_int
    _ = (P.skewMeasure.real M * ∫ x in slab, (f x : ℝ) : ℝ) := by
      simp only [inner, integral_complex_ofReal, integral_const_mul, integral_indicator slab_meas]
    _ = _ := by
      change _ = ((P.skewMeasure M * ∫⁻ x in slab, (f x : ℝ≥0∞)).toReal : ℂ)
      rw [toReal_mul, lintegral_coe_eq_integral _ f_int.restrict,
        toReal_ofReal (integral_nonneg fun x ↦ (f x).coe_nonneg), Measure.real]

/-- Let the family `l` of measures on the quadrics, indexed by skew elements, disintegrate Haar
measure along `x ↦ x* J x`, let `δ = P.skewUnit` and let `t` be skew. For continuous `f ≥ 0`, the
mass of `f` on the slab where `c δ (x* J x - δ⁻¹ t)` is integral is the integral of the masses of
`f` on the quadrics with index `t + b`, over the skew `b` with `c b` integral. -/
lemma Place.IsDisintegration.setLIntegral_slab (h : P.IsDisintegration volume J l)
    {f : (κ → A) → ℝ≥0} (hf : Continuous f) (c : A) (t : skewAdjoint A) :
    ∫⁻ x : κ → A in {x : κ → A | c * (P.skewUnit * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t)) ∈ O},
      f x =
      ∫⁻ b : skewAdjoint A in {b : skewAdjoint A | c * b.1 ∈ O},
        ∫⁻ x : κ → A, f x ∂l (b + t) ∂P.skewMeasure := by
  let W : Set A := {a | c * (P.skewUnit * (a - P.skewUnit⁻¹.1 * t)) ∈ O}
  have W_meas : MeasurableSet W := isOpen_O.measurableSet.preimage (by fun_prop)
  have mem_W (b : skewAdjoint A) : P.skewUnit⁻¹.1 * (b.1 + t.1) ∈ W ↔ c * b.1 ∈ O := by
    simp [W, ← mul_sub]
  -- Write both restrictions as indicators; both sets are preimages of the open set `O`.
  have slab_meas : MeasurableSet
      {x : κ → A | c * (P.skewUnit * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t)) ∈ O} :=
    isOpen_O.measurableSet.preimage (by fun_prop)
  have cut_meas : MeasurableSet {b : skewAdjoint A | c * b.1 ∈ O} :=
    isOpen_O.measurableSet.preimage (by fun_prop)
  rw [← lintegral_indicator slab_meas, ← lintegral_indicator cut_meas]
  calc
    _ = ∫⁻ x, W.indicator 1 (star x ⬝ᵥ J *ᵥ x) * f x := by simp [W, indicator]
    _ = ∫⁻ b, ∫⁻ x, W.indicator 1 (P.skewUnit⁻¹.1 * b.1) * f x ∂l b ∂P.skewMeasure :=
      h.lintegral_eq (fun p ↦ W.indicator 1 p.1 * f p.2) (by fun_prop (disch := exact W_meas))
    _ = ∫⁻ b, ∫⁻ x, W.indicator 1 (P.skewUnit⁻¹.1 * (b + t).1) * f x ∂l (b + t) ∂P.skewMeasure :=
      (lintegral_add_right_eq_self _ t).symm
    _ = _ := lintegral_congr fun b ↦ by
      by_cases hb : c * b.1 ∈ O <;> simp [indicator, mem_W, hb]

/-- The mean of a continuous function over the skew elements `t + b` with `b ∈ y ȳ O` tends to its
value at `t` as the unit `y` tends to zero. The factor, the measure of the `b` with `y ȳ b ∈ O`, is
the inverse of the measure of the skew elements of `y ȳ O`. -/
lemma IntegralPlace.tendsto_average_skew {g : skewAdjoint A → ℝ≥0∞} (hg : Continuous g)
    (t : skewAdjoint A) :
    Tendsto (fun y : Aˣ ↦ P.skewMeasure {b : skewAdjoint A | (y * star y).1 * b.1 ∈ O} *
        ∫⁻ b : skewAdjoint A in {b : skewAdjoint A | (y * star y)⁻¹.1 * b.1 ∈ O},
          g (b + t) ∂P.skewMeasure)
      (comap Units.val (𝓝 0)) (𝓝 (g t)) := by
  have u_star (y : Aˣ) : star (y * star y).1 = (y * star y).1 := by simp [mul_comm]
  have u_inv_star (y : Aˣ) : star (y * star y)⁻¹.1 = (y * star y)⁻¹.1 := by
    simp [← Units.coe_star_inv, mul_comm]
  -- The two sets have reciprocal measures, so the mean of a constant is that constant.
  have mean_const (y : Aˣ) (a : ℝ≥0∞) : P.skewMeasure {b | (y * star y).1 * b.1 ∈ O} *
      ∫⁻ _ in {b : skewAdjoint A | (y * star y)⁻¹.1 * b.1 ∈ O}, a ∂P.skewMeasure = a := by
    rw [setLIntegral_const, P.skewMeasure_setOf_mul_mem _ (u_star y),
      P.skewMeasure_setOf_mul_mem _ (u_inv_star y), P.modulus_inv, ENNReal.inv_rpow, inv_inv]
    -- The goal is `r⁻¹ * (a * r) = a` with `r = modulus (y * star y) ^ (1 / 2)`.
    rw [mul_left_comm, ENNReal.inv_mul_cancel (by simp) (by simp [mul_eq_top]), mul_one]
  -- The values of `g` on these elements lie in any given neighbourhood of `g t` if `y` is small.
  have near {V : Set ℝ≥0∞} (hV : V ∈ 𝓝 (g t)) : ∀ᶠ y : Aˣ in comap Units.val (𝓝 0),
      ∀ b : skewAdjoint A, (y * star y)⁻¹.1 * b.1 ∈ O → g (b + t) ∈ V := by
    have h_cont : Continuous fun z : A × A ↦
        g (skewPart (P.element * (z.1 * star z.1) * z.2) + t) := by fun_prop
    have small : ∀ᶠ y in 𝓝 (0 : A), ∀ r ∈ (P.integers : Set A),
        g (skewPart (P.element * (y * star y) * r) + t) ∈ V := by
      refine isCompact_O.eventually_forall_of_forall_eventually fun r _ ↦ ?_
      -- At `y = 0` the argument of `g` is `t`.
      exact h_cont.tendsto' (0, r) (g t) (congrArg g (by ext; simp)) hV
    filter_upwards [tendsto_comap small] with y hy b hb
    have b_eq : skewPart (P.element * (y * star y).1 * ((y * star y)⁻¹.1 * b.1)) = b := by
      ext
      rw [mul_assoc, Units.mul_inv_cancel_left]
      simp [skewAdjoint.star_val_eq, ← add_mul]
    rw [← b_eq]
    exact hy _ hb
  have ball_meas (y : Aˣ) : MeasurableSet {b : skewAdjoint A | (y * star y)⁻¹.1 * b.1 ∈ O} :=
    isOpen_O.measurableSet.preimage (by fun_prop)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun a ha ↦ ?_⟩
  · obtain ⟨a', ha_lt, ha'_lt⟩ : ∃ a' : ℝ≥0∞, a < a' ∧ a' < g t := exists_between ha
    filter_upwards [near (Ioi_mem_nhds ha'_lt)] with y hy
    refine ha_lt.trans_le ?_
    rw [← mean_const y a']
    exact mul_le_mul_right (setLIntegral_mono' (ball_meas y) fun b hb ↦ (hy b hb).le) _
  · obtain ⟨a', ha'_lt, ha_lt⟩ : ∃ a' : ℝ≥0∞, g t < a' ∧ a' < a := exists_between ha
    filter_upwards [near (Iio_mem_nhds ha'_lt)] with y hy
    refine lt_of_le_of_lt ?_ ha_lt
    rw [← mean_const y a']
    exact mul_le_mul_right (setLIntegral_mono' (ball_meas y) fun b hb ↦ (hy b hb).le) _

/-- Fourier inversion for local densities. Let the measures `l b`, indexed by skew `b`, disintegrate
Haar measure along `x ↦ x* J x` for a hermitian `J`, let `ψ` be trivial on traces, and let `f ≥ 0`
be continuous of compact support. Put `δ = P.skewUnit` and let `t` be skew. If the function
`b ↦ ∫ f(x) ψ(e b (x* J x - δ⁻¹ t)) dx` is integrable on the skew elements, its integral, the
density of `f` at `δ⁻¹ t`, is the integral of `f` against `l t`. Here `e = P.element` and
`e + ē = 1`. -/
theorem IntegralPlace.integral_skewMeasure_eq_toReal_lintegral (h : P.IsDisintegration volume J l)
    (hJ : Jᴴ = J) (hψ : ∀ x : A, P.ψ (x + star x) = 1) {f : (κ → A) → ℝ≥0} (hf : Continuous f)
    (h_supp : HasCompactSupport f) (t : skewAdjoint A)
    (h_int : Integrable (fun b : skewAdjoint A ↦ ∫ x : κ → A,
      f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t))) P.skewMeasure) :
    ∫ b : skewAdjoint A, ∫ x : κ → A,
      f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t))
      ∂volume ∂P.skewMeasure = (∫⁻ x : κ → A, f x ∂l t).toReal := by
  -- Cut the frequency to `y ȳ b ∈ O`. The cut integral is the mean of the masses of the quadrics
  -- with index in `t + y ȳ O`. Let the unit `y` tend to zero.
  obtain ⟨(mass_cont : Continuous fun b : skewAdjoint A ↦ ∫⁻ x, f x ∂l b),
      (mass_fin : ∀ b : skewAdjoint A, ∫⁻ x, f x ∂l b < ∞)⟩ := h.continuous_and_lt_top hf h_supp
  -- Units are dense, so they can tend to zero.
  have units_neBot : (comap Units.val (𝓝 (0 : A))).NeBot := comap_neBot fun s hs ↦ by
    simpa [Set.Nonempty, IsUnit, and_comm] using
      (dense_of_ae P.ae_isUnit).inter_nhds_nonempty hs
  let cut (y : Aˣ) : Set (skewAdjoint A) := {b | (y * star y).1 * b.1 ∈ O}
  have cover : AECover P.skewMeasure (comap Units.val (𝓝 0)) cut := by
    refine ⟨.of_forall fun b ↦ ?_, fun _ ↦ isOpen_O.measurableSet.preimage (by fun_prop)⟩
    have h_small : Tendsto (fun y : A ↦ y * star y * b.1) (𝓝 0) (𝓝 0) :=
      Continuous.tendsto' (by fun_prop) 0 0 (by simp)
    exact tendsto_comap.eventually (h_small.eventually (isOpen_O.mem_nhds (zero_mem O)))
  have h_cut (y : Aˣ) :
      ∫ b in cut y, ∫ x, f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t))
          ∂volume ∂P.skewMeasure =
        (P.skewMeasure (cut y) * ∫⁻ b in {b : skewAdjoint A | (y * star y)⁻¹.1 * b.1 ∈ O},
          ∫⁻ x, f x ∂l (b + t) ∂P.skewMeasure).toReal := by
    rw [← h.setLIntegral_slab hf]
    exact setIntegral_eq_slab hJ hψ hf h_supp (by simp [mul_comm])
      (by simp [skewAdjoint.star_val_eq])
  have h_mean : Tendsto (fun y : Aˣ ↦ (P.skewMeasure (cut y) *
      ∫⁻ b in {b : skewAdjoint A | (y * star y)⁻¹.1 * b.1 ∈ O}, ∫⁻ x, f x ∂l (b + t)
        ∂P.skewMeasure).toReal) (comap Units.val (𝓝 0)) (𝓝 (∫⁻ x, f x ∂l t).toReal) :=
    (tendsto_toReal (mass_fin t).ne).comp (tendsto_average_skew mass_cont t)
  -- The cut integrals tend both to the full integral and to the mass of the quadric.
  refine tendsto_nhds_unique (cover.integral_tendsto_of_countably_generated h_int) ?_
  simp only [h_cut]
  exact (Complex.continuous_ofReal.tendsto _).comp h_mean

/-- The density of `f ≥ 0` has norm at most the integral of `f` over the quadric. If the outer
integrand is not integrable, the left side is zero by convention.

This is a one-sided form of Fourier inversion for the fiber integrals of a hermitian form at finite
places: an upper bound in norm, for continuous `f ≥ 0` of compact support, rather than an
equality. -/
lemma IntegralPlace.enorm_localDensity_le (h : P.IsDisintegration volume J l) (hJ : Jᴴ = J)
    (hψ : ∀ x : A, P.ψ (x + star x) = 1) {f : (κ → A) → ℝ≥0} (hf : Continuous f)
    (h_supp : HasCompactSupport f) (t : skewAdjoint A) :
    ‖∫ b : skewAdjoint A, ∫ x : κ → A,
      f x * P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t))
      ∂volume ∂P.skewMeasure‖ₑ ≤ ∫⁻ x : κ → A, f x ∂l t := by
  by_cases h_int : Integrable (fun b : skewAdjoint A ↦ ∫ x, f x *
      P.ψ (P.element * b.1 * (star x ⬝ᵥ J *ᵥ x - P.skewUnit⁻¹.1 * t))) P.skewMeasure
  · simp [integral_skewMeasure_eq_toReal_lintegral h hJ hψ hf h_supp t h_int, ← ofReal_norm,
    ofReal_toReal_le]
  · simp [integral_undef h_int]

end Inversion

/-- For s-finite, translation-invariant measures `μ` on `X` and `ν` on `Y` (additive groups, with
`ν` also invariant under negation), let measurable maps `ι : Y → X` and `p : X → Y` satisfy
`p (ι y + x) = y + p x`, and let `K` be a measurable set with `ν K = 1`. If
`f (ι y + x) = c x * a (y + p x)` whenever `p x ∈ K`, then `∫ f ∂μ` equals the product of `∫ c ∂μ`
over `p ⁻¹' K` and `∫ a ∂ν`. -/
lemma integral_eq_mul_of_section {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableAdd₂ X] [MeasurableNeg X]
    [MeasurableAdd₂ Y] [MeasurableNeg Y] {μ : Measure X} (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsAddLeftInvariant] [ν.IsAddLeftInvariant] [ν.IsNegInvariant] {ι : Y → X} {p : X → Y}
    (hι : Measurable ι) (hp : Measurable p) (h_sec : ∀ (y : Y) (x : X), p (ι y + x) = y + p x)
    {K : Set Y} (hK : MeasurableSet K) (K_one : ν K = 1) {f c : X → ℂ} {a : Y → ℂ}
    (hf : ∀ (y : Y) (x : X), p x ∈ K → f (ι y + x) = c x * a (y + p x)) :
    ∫ x : X, f x ∂μ = (∫ x : X in p ⁻¹' K, c x ∂μ) * ∫ y : Y, a y ∂ν := by
  -- The map `e (x, y) = (ι (y - p x) + x, p x)` preserves `μ × ν` and carries
  -- `f (x) * 𝟙_K (y)` back to `𝟙_(p ⁻¹' K) (x) * c x * a (y)`.
  have h_sub (x : X) (y : Y) : p (x - ι y) = p x - y := by
    simpa [eq_sub_iff_add_eq'] using (h_sec y (x - ι y)).symm
  let e : X × Y ≃ᵐ X × Y :=
    { toFun q := (ι (q.2 - p q.1) + q.1, p q.1)
      invFun q := (q.1 - ι (p q.1 - q.2), p q.1)
      left_inv _ := by simp [h_sec]
      right_inv _ := by simp [h_sub]
      measurable_toFun := by dsimp; fun_prop
      measurable_invFun := by dsimp; fun_prop }
  have shear₁ : MeasurePreserving (fun q : X × Y ↦ (q.1, q.2 - p q.1)) (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).skew_product (g := fun x y ↦ y - p x) (by fun_prop)
      (.of_forall fun x ↦ map_sub_right_eq_self ν (p x))
  have shear₂ : MeasurePreserving (fun q : Y × X ↦ (q.1, ι q.1 + q.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun y x ↦ ι y + x) (by fun_prop)
      (.of_forall fun y ↦ map_add_left_eq_self μ (ι y))
  have shear₃ : MeasurePreserving (fun q : X × Y ↦ (q.1, p q.1 - q.2)) (μ.prod ν) (μ.prod ν) :=
    (MeasurePreserving.id μ).skew_product (g := fun x y ↦ p x - y) (by fun_prop)
      (.of_forall fun x ↦ ν.map_sub_left_eq_self (p x))
  have he : MeasurePreserving e (μ.prod ν) (μ.prod ν) := by
    have e_eq : ⇑e = (fun q ↦ (q.1, p q.1 - q.2)) ∘ Prod.swap ∘ (fun q ↦ (q.1, ι q.1 + q.2)) ∘
        Prod.swap ∘ fun q ↦ (q.1, q.2 - p q.1) := by
      ext q <;> simp [e, h_sec]
    rw [e_eq]
    exact shear₃.comp (measurePreserving_swap.comp
      (shear₂.comp (measurePreserving_swap.comp shear₁)))
  calc
    _ = ∫ q : X × Y, f q.1 * K.indicator 1 q.2 ∂μ.prod ν := by
      simp [integral_prod_mul f, integral_indicator hK, K_one, Measure.real]
    _ = ∫ q : X × Y, (p ⁻¹' K).indicator c q.1 * a q.2 ∂μ.prod ν := by
      rw [← he.integral_comp']
      refine integral_congr_ae (.of_forall fun q ↦ ?_)
      by_cases hq : p q.1 ∈ K <;> simp [e, hf, hq]
    _ = _ := by rw [integral_prod_mul, integral_indicator (hp hK)]

end New.Floors
