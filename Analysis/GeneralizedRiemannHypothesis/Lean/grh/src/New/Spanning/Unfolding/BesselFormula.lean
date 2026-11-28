import Lib.Weil.Periods.Equivariant
import New.Spanning.Unfolding.PoincareSeries

/-!
# The Bessel function as an integral over `R(F_∞)`

The group `R(F_∞)` is the product of the groups `R` at the infinite places. So the tensor product of
the local Bessel functions, each an integral over `R`, is one integral over `R(F_∞)`.

Notions from other files:
* `GInf E ε` is `G(F_∞)`, one copy of `U(diag ε)` for each infinite place of `E`, and `New.G E ε` is
  the adelic group `G(F_∞) × G(𝔸_f)` of the hermitian space `V`. The group `𝔰.G₁` is the complex
  unitary group of `ϱ` hyperbolic planes, the positive form with basis `𝔰.κ` and a negative vector.
* `S.Fits V l kw Y η`: the grading `Y` of `V` is standardly indexed, the Bessel system of the
  filling data `S` at each infinite place `v` has type `(l v, kw v)`, the kernel `typeKernel l ε` is
  idempotent, and the finite part of `V.x` is described by `S` and the central element `η`.
* `Y.besselGroup` is `R = U ⋊ H`, with `U = Y.unipotent` and `H` the unitary group of `κ`, embedded
  by `Y.inclX`; `Y.leviPart (n * Y.inclX a) = a`, and `Y.besselReal` is the group `R(F_∞)` of the
  real points of `R`.
* `𝔰.besselGraph` is the local group `R`, as pairs `(g, a)` in `G₁ × U(κ)` with `g (embedH a)⁻¹` in
  the local unipotent group `besselU`.
* `S.adelicToInf` takes the components at the infinite places in rescaled bases, and
  `h.realHomeomorph` identifies `G(F_∞)` with the product of copies of `G₁`: at each place it
  changes the basis and multiplies on the left by a fixed element, made from the distinguished
  matrix `V.x` of `V`.
* `𝔰.besselGraphMeasure` is the Haar measure `du dh` on the local group `R`, and
  `(l v).dsCoeffInFrame` is the coefficient of the discrete series of parameter `l v` on `G₁`.
* `S.besselSystem v` is the Bessel system at `v`. Its functions take values in `ℂ^I`, with
  `I = (S.besselSystem v).Index` finite, and `U(κ)` acts on `ℂ^I` by the unitary matrices
  `(S.besselSystem v).rep`. An element of `S.BesselCoord` is a choice of one index in `I` at each
  `v`, so `S.BesselCoord → ℂ` is the tensor product of the spaces `ℂ^I`.
* `WeylIndex 𝔰.κ kw` indexes a basis of the Weyl module of weight `kw`, in which forms take values.
* `h.weylBesselEquiv` is a fixed linear identification of the values of forms with the dual of the
  values of the Bessel function, and `ψ_U` is the generic character of `Y.unipotent`.

## Relation to the literature

Related work on Bessel periods and on second moments is listed in `New.Spanning.Unfolding.Moments`.
-/

open MeasureTheory Measure Matrix ComplexConjugate NumberField

noncomputable section

namespace New

/-- The dot product of a vector `a` with the tensor product of finitely many vector-valued integrals
`∫ f v` is one integral over the product space, if each `f v` is integrable. -/
lemma dotProduct_prod_integral {T X : Type} [Fintype T] [DecidableEq T] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] {I : T → Type} [∀ v : T, Fintype (I v)]
    {f : ∀ v : T, X → EuclideanSpace ℂ (I v)} (hf : ∀ v : T, Integrable (f v) μ)
    (a : (∀ v : T, I v) → ℂ) :
    a ⬝ᵥ (fun i : ∀ v : T, I v ↦ ∏ v : T, (∫ s : X, f v s ∂μ) (i v)) =
      ∫ q : T → X, a ⬝ᵥ (fun i : ∀ v : T, I v ↦ ∏ v : T, f v (q v) (i v))
        ∂Measure.pi fun _ : T ↦ μ := by
  have h_coord (v : T) (i : I v) : Integrable (fun s ↦ f v s i) μ := (hf v).eval_piLp i
  simp only [dotProduct, eval_integral_piLp (h_coord _), ← integral_fintype_prod_eq_prod,
    ← integral_const_mul]
  exact (integral_finsetSum _ fun i _ ↦
    (Integrable.fintype_prod_dep fun v ↦ h_coord v (i v)).const_mul (a i)).symm

/-- The unitary group of the standard form, written with signs all equal to one, is isomorphic to
the one written with the unit matrix, by the identity on matrices. -/
def unitSignEquiv (n : Type) [Fintype n] [DecidableEq n] :
    USign (1 : n → ℤˣ) ≃ₜ* U (1 : Matrix n n ℂ) where
  __ := MulEquiv.subgroupCongr (congrArg U signMatrix_one)
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The isomorphism `unitSignEquiv` does not change the matrix. -/
lemma coe_unitSignEquiv {n : Type} [Fintype n] [DecidableEq n] (u : USign (1 : n → ℤˣ)) :
    (unitSignEquiv n u : GL n ℂ) = u := rfl

namespace Filling.Fits

open RealPlace DiscreteSeries

variable {E : Type} {𝔰 : Shape} [Field E] [CMType E] {S : Filling E 𝔰}
  {ε : 𝔰.BesselIndex → ℤˣ} {l : InfinitePlace E → HCParam ε}
  {kw : InfinitePlace E → ℕ → ℕ} {V : Space E 𝔰.BesselIndex ε}
  {Y : Grading V S.N 𝔰.κ (2 * 𝔰.ϱ + 1)} {η : Gf E 𝔰.κ} [UnitarySignFrame 𝔰 ε]

/-! ### The group `R(F_∞)` place by place -/

/-- The homomorphism that takes a real point of the group of `V` to the components at the infinite
places (`S.adelicToInf`) of its image in the adelic group of `S` (`h.adelicEquiv`). At each place it
is a conjugation that carries `U(diag ε)` onto `G₁`. -/
def realCoords (h : S.Fits V l kw Y η) : GInf E ε →* InfinitePlace E → 𝔰.G₁ :=
  S.adelicToInf.comp (h.adelicEquiv.toMonoidHom.comp (MonoidHom.inl _ _))

/-- The homeomorphism `realHomeomorph` turns left translation by `s` into left translation by
`realCoords s`. -/
lemma realCoords_mul_realHomeomorph (h : S.Fits V l kw Y η) (s y : GInf E ε) :
    h.realCoords s * h.realHomeomorph y = h.realHomeomorph (s * y) :=
  (h.realHomeomorph_mul (s, 1) (y, 1)).symm

/-- The map `realCoords` as a homeomorphism: it is `realHomeomorph` followed by right multiplication
by the inverse of its value at one. -/
def realCoordsHomeomorph (h : S.Fits V l kw Y η) : GInf E ε ≃ₜ (InfinitePlace E → 𝔰.G₁) :=
  h.realHomeomorph.trans (Homeomorph.mulRight (h.realHomeomorph 1)⁻¹)

lemma coe_realCoordsHomeomorph (h : S.Fits V l kw Y η) :
    ⇑h.realCoordsHomeomorph = h.realCoords := by
  simp [funext_iff, realCoordsHomeomorph, mul_inv_eq_iff_eq_mul, realCoords_mul_realHomeomorph]

lemma isEmbedding_realCoords (h : S.Fits V l kw Y η) : Topology.IsEmbedding h.realCoords := by
  simpa only [coe_realCoordsHomeomorph] using h.realCoordsHomeomorph.isEmbedding

/-- Let `g` lie in `Y.unipotent`, the adelic unipotent group of the grading `Y` of `V`. Carry `g` to
the adelic unitary group of `S` by `h.adelicEquiv`. Then its component in `G₁` at each infinite
place `v` lies in `besselU`, the block upper unitriangular subgroup of `G₁`. -/
lemma adelicToInf_mem_besselU (h : S.Fits V l kw Y η) {g : New.G E ε} (hg : g ∈ Y.unipotent)
    (v : InfinitePlace E) :
    S.adelicToInf (h.adelicEquiv g) v ∈ besselU :=
  -- The diagonal change of basis at `v` keeps a matrix unitriangular.
  conj_mem_unitriangular (blockTriangular_diagonal _)
    ((h.mem_unipotent_iff_mem_besselU.mp hg).map_mem_agreeWithOneOn _)

/-- Suppose the hermitian space `V` of signs `ε` with grading `Y` fits the filling data `S` (the
hypothesis `h`), so that `h.adelicEquiv` identifies the adelic unitary group `New.G E ε` of `V` with
that of `S`. A point `g` with trivial finite part lies in the unipotent group `Y.unipotent` if, at
each infinite place, the component in `G₁` (`adelicToInf`) of its image under `h.adelicEquiv` lies
in `besselU`, the block upper unitriangular subgroup of `G₁`. -/
lemma mem_unipotent_of_snd_eq_one (h : S.Fits V l kw Y η) {g : New.G E ε} (h_fin : g.2 = 1)
    (h_inf : ∀ v : InfinitePlace E, S.adelicToInf (h.adelicEquiv g) v ∈ besselU) :
    g ∈ Y.unipotent := by
  refine h.mem_unipotent_iff_mem_besselU.mpr (mem_besselU.2 fun a b hab ↦ Prod.ext ?_ ?_)
  · -- The entries at the infinite places.
    ext v
    have h_entry : ((h.adelicEquiv g).val a b).1 v * (S.basisScale v b / S.basisScale v a) =
        (1 : Matrix 𝔰.BesselIndex 𝔰.BesselIndex ℂ) a b := by
      simpa only [S.adelicToInf_apply] using mem_besselU.1 (h_inf v) a b hab
    rcases eq_or_ne a b with rfl | h_ne
    · simpa using h_entry
    · simpa [one_apply, h_ne] using h_entry
  · -- The entries at the finite places.
    have h_matrix : ((h.adelicEquiv g).val a b).2 = V.ratCoordMatrixFin g.2 a b :=
      (congrFun₂ (V.ratCoordMatrixFin_snd g) a b).symm
    simp [h_matrix, h_fin, Space.ratCoordMatrixFin, one_apply, apply_ite]

/-- Let `s` be a real point of the group of `V`, and `a` an adelic point of the unitary group `H` of
the definite form on `𝔰.κ`, embedded by `Y.inclX`. The component in `G₁` at `v` of the adelic point
`(s, 1) * (Y.inclX a)⁻¹` is `realCoords s v`, the component of `(s, 1)`, times the inverse of the
component `a.1 v` of `a`, embedded in `G₁` by `embedH`. -/
lemma adelicToInf_mul_inv_inclX (h : S.Fits V l kw Y η) (s : GInf E ε)
    (a : New.G E (1 : 𝔰.κ → ℤˣ)) (v : InfinitePlace E) :
    S.adelicToInf (h.adelicEquiv ((s, 1) * (Y.inclX a)⁻¹)) v =
      h.realCoords s v * (embedH (unitSignEquiv 𝔰.κ (a.1 v)))⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_inv, h.adelicToInf_inclX]
  -- Both sides put the same matrix into the middle block.
  rfl

/-- The components at the infinite places of an element `s` of `R(F_∞)`: the pair of the component
of `s` in `G₁` and of its Levi part in `U(κ)`. -/
def besselRealToPi (h : S.Fits V l kw Y η) :
    Y.besselReal →* InfinitePlace E → 𝔰.besselGraph :=
  .mk' (fun s v ↦ ⟨(h.realCoords s v, unitSignEquiv 𝔰.κ ((Y.leviPart ⟨(s.1, 1), s.2⟩).1 v)), by
      rw [Shape.mem_besselGraph_iff_mul_inv_mem, ← h.adelicToInf_mul_inv_inclX]
      exact h.adelicToInf_mem_besselU (Y.mul_inv_inclX_leviPart_mem ⟨(s.1, 1), s.2⟩) v⟩)
    fun s t ↦ by
      have h_levi : Y.leviPart ⟨((s * t).1, 1), (s * t).2⟩ =
          Y.leviPart ⟨(s.1, 1), s.2⟩ * Y.leviPart ⟨(t.1, 1), t.2⟩ := by
        rw [← map_mul]
        exact congrArg _ (Subtype.ext (by simp))
      ext v : 3
      · simp
      · simp only [h_levi]
        exact map_mul _ _ _

/-- The component in `G₁` at `v` of `besselRealToPi s` is that of `s`. -/
lemma besselRealToPi_apply_fst (h : S.Fits V l kw Y η) (s : Y.besselReal) (v : InfinitePlace E) :
    (h.besselRealToPi s v).val.fst = h.realCoords s v := rfl

/-- The component in `U(κ)` at `v` of `besselRealToPi s` is that of the Levi part of `s`. -/
lemma besselRealToPi_apply_snd (h : S.Fits V l kw Y η) (s : Y.besselReal) (v : InfinitePlace E) :
    (h.besselRealToPi s v).val.snd =
      unitSignEquiv 𝔰.κ ((Y.leviPart ⟨(s.val, 1), s.property⟩).fst v) := rfl

/-- The map `besselRealToPi` is continuous, as both components at each place are. -/
lemma continuous_besselRealToPi (h : S.Fits V l kw Y η) : Continuous h.besselRealToPi := by
  have h_coords : Continuous h.realCoords := h.isEmbedding_realCoords.continuous
  have h_levi : Continuous fun s : Y.besselReal ↦ Y.leviPart ⟨(s.1, 1), s.2⟩ :=
    Y.continuous_leviPart.comp (by fun_prop)
  refine continuous_pi fun v ↦ continuous_induced_rng.2 ?_
  change Continuous fun s : Y.besselReal ↦
    (h.realCoords s v, unitSignEquiv 𝔰.κ ((Y.leviPart ⟨(s.1, 1), s.2⟩).1 v))
  fun_prop

/-- Suppose the hermitian space `V` with grading `Y` fits the filling data `S`. Then
`besselRealToPi` is surjective: it maps `Y.besselReal`, the real points of the Bessel group
`R = U ⋊ H` of `Y`, onto the product over the infinite places of the local Bessel group
`𝔰.besselGraph`. -/
lemma besselRealToPi_surjective (h : S.Fits V l kw Y η) :
    Function.Surjective h.besselRealToPi := by
  -- Take the real point `s` of `G` and the real point `a` of `H` with the given components. Then
  -- `s a⁻¹` lies in `U` at each place, so `s` lies in `R` and has the Levi part `a`.
  intro q
  obtain ⟨s, hs⟩ : ∃ s : GInf E ε, h.realCoords s = fun v : InfinitePlace E ↦ (q v).val.1 := by
    simpa only [coe_realCoordsHomeomorph] using h.realCoordsHomeomorph.surjective fun v ↦
      (q v).val.1
  let a : GInf E (1 : 𝔰.κ → ℤˣ) := fun v ↦ (unitSignEquiv 𝔰.κ).symm (q v).val.2
  have ha_fin : (Y.inclX (a, 1)).2 = 1 := h.finiteEquiv.injective (by simp [h.finiteEquiv_inclX])
  have h_unip : (s, 1) * (Y.inclX (a, 1))⁻¹ ∈ Y.unipotent := by
    refine h.mem_unipotent_of_snd_eq_one (by simp [ha_fin]) fun v ↦ ?_
    rw [h.adelicToInf_mul_inv_inclX, hs, ContinuousMulEquiv.apply_symm_apply]
    exact Shape.mem_besselGraph_iff_mul_inv_mem.1 (q v).2
  have h_mem : (s, 1) ∈ Y.besselGroup := by
    simpa using mul_mem (Y.unipotent_le_besselGroup h_unip) (Y.inclX_mem_besselGroup (a, 1))
  have h_levi : Y.leviPart ⟨(s, 1), h_mem⟩ = (a, 1) := by
    simpa using Y.leviPart_mul_inclX h_unip (a, 1)
  refine ⟨⟨s, h_mem⟩, ?_⟩
  ext v : 3
  · rw [besselRealToPi_apply_fst, hs]
  · simp [besselRealToPi_apply_snd, h_levi, a]

/-- The group `R(F_∞)` is the product of the groups `R` at the infinite places: `besselRealToPi` as
an isomorphism of topological groups. -/
def besselRealEquiv (h : S.Fits V l kw Y η) :
    Y.besselReal ≃ₜ* (InfinitePlace E → 𝔰.besselGraph) :=
  -- The first components of the image are given by `realCoords`, an embedding of `G(F_∞)`.
  have h_emb : Topology.IsEmbedding h.besselRealToPi :=
    .of_comp h.continuous_besselRealToPi (g := fun q (v : InfinitePlace E) ↦ (q v).val.1)
      (by fun_prop) (h.isEmbedding_realCoords.comp .subtypeVal)
  { h_emb.toHomeomorphOfSurjective h.besselRealToPi_surjective with
    map_mul' := h.besselRealToPi.map_mul }

/-- Suppose the hermitian space `V` with grading `Y` fits the filling data `S` (the hypothesis `h`),
so that `besselRealToPi` identifies `Y.besselReal`, the real points of the Bessel group `R = U ⋊ H`,
with a product of copies of the local Bessel group `𝔰.besselGraph`. The latter has the Haar measure
`𝔰.besselGraphMeasure`, a product of Haar measures on its unipotent and Levi factors. For a real
constant `c`, the integral of any `F` against the product of these measures is `c` times the
integral of `F ∘ besselRealToPi` against the Haar measure `haar` of `Y.besselReal`. -/
lemma exists_integral_pi_eq (h : S.Fits V l kw Y η) :
    ∃ c : ℝ, ∀ F : (InfinitePlace E → 𝔰.besselGraph) → ℂ,
      ∫ q : InfinitePlace E → 𝔰.besselGraph, F q
          ∂(Measure.pi fun _ : InfinitePlace E ↦ 𝔰.besselGraphMeasure) =
        c * ∫ s : Y.besselReal, F (h.besselRealToPi s) ∂haar := by
  -- Both sides come from Haar measures on the product of the local groups, so they are
  -- proportional.
  let μ : Measure (InfinitePlace E → 𝔰.besselGraph) := Measure.pi fun _ ↦ 𝔰.besselGraphMeasure
  let ν : Measure (InfinitePlace E → 𝔰.besselGraph) := haar.map h.besselRealEquiv
  have : MeasurableMul 𝔰.besselGraph := ContinuousMul.measurableMul
  have : μ.IsHaarMeasure := Measure.pi.isHaarMeasure _
  have : ν.IsHaarMeasure := h.besselRealEquiv.isHaarMeasure_map haar
  refine ⟨haarScalarFactor μ ν, fun F ↦ ?_⟩
  have h_map : ∫ q, F q ∂ν = ∫ s : Y.besselReal, F (h.besselRealToPi s) ∂haar :=
    h.besselRealEquiv.toHomeomorph.measurableEmbedding.integral_map F
  calc _ = ∫ q, F q ∂(haarScalarFactor μ ν • ν) := by rw [← isMulLeftInvariant_eq_smul μ ν]
    _ = _ := by rw [integral_smul_nnreal_measure, h_map, NNReal.smul_def, Complex.real_smul]

/-! ### The three factors of the integrand -/

/-- The standard additive character of `E` at `-(M ϖ)⁻¹` times the sum `simpleRootSum` of the
entries at the simple roots of the image of `r` in the adelic group of `S`. Here `M = S.M` is the
product of the two level primes and `ϖ = S.deltaE` is the chosen generator of the different of `E`.
On `R(𝔸)` this is a character that is trivial on `H(𝔸)`; it extends `ψ_U` when the constant
`c = Y.genericConst` of `ψ_U` satisfies `ȷ * c = -(M ϖ)⁻¹`, where `ȷ = WeilData.j` is the purely
imaginary element of `E` fixed by the Weil data. -/
def besselChar (h : S.Fits V l kw Y η) (r : New.G E ε) : ℂ :=
  stdAddChar E (toAdele (-(S.M * S.deltaE : E)⁻¹) * simpleRootSum (h.adelicEquiv r))

/-- Suppose `V` fits `S`. Let `s` be a point of `GInf E ε = ∏_v U(diag ε)`, so that `(s, 1)` is the
adelic point with infinite part `s` and trivial finite part, and let `g_v = realCoords s v` be its
conjugate in the complex unitary group `G₁` at `v`. The inverse of `besselChar (s, 1)` is the
product over `v` of `wave (-simpleRootSum g_v)`. -/
lemma besselChar_inl_inv (h : S.Fits V l kw Y η) (s : GInf E ε) :
    (h.besselChar (s, 1))⁻¹ = ∏ v : InfinitePlace E, wave (-simpleRootSum (h.realCoords s v)) := by
  set x : S.G (𝔸 E) := h.adelicEquiv (s, 1) with hx
  set z : 𝔸 E := toAdele (-(S.M * S.deltaE : E)⁻¹) * simpleRootSum x with hz
  have hx_fin : S.adelicToFin x = 1 := by
    simpa [← hx, mul_assoc, eq_inv_mul_iff_mul_eq] using h.finiteEquiv_eq_conj_adelicToFin (s, 1)
  have hz_fin : z.2 = 0 := by
    simp [hz, ← S.simpleRootSum_adelicToFin, hx_fin, simpleRootSum_eq_zero_of_mem_besselH]
  have hz_inf (v : InfinitePlace E) :
      simpleRootSum (h.realCoords s v) = -Real.pi * 2 * Complex.I * z.1 v :=
    S.simpleRootSum_adelicToInf x v
  -- With `c = 2πi z_v` one has `c - c̄ = 2πi · 2 Re z_v`; multiply over the infinite places.
  have h_wave (v : InfinitePlace E) : wave (-simpleRootSum (h.realCoords s v)) =
      Complex.exp (2 * Real.pi * Complex.I * (2 * (z.1 v).re : ℝ)) := by
    rw [wave, hz_inf, Complex.sub_conj]
    exact congrArg Complex.exp (by simp [Complex.ext_iff, mul_assoc, mul_left_comm])
  calc (h.besselChar (s, 1))⁻¹ = (stdAddChar E z : ℂ)⁻¹ := rfl
    _ = Complex.exp (∑ v, 2 * Real.pi * Complex.I * (2 * (z.1 v).re : ℝ)) := by
        simp [stdAddChar, hz_fin, ← Complex.exp_neg, Finset.mul_sum, mul_assoc, mul_comm Complex.I]
    _ = ∏ v, wave (-simpleRootSum (h.realCoords s v)) := by simp only [Complex.exp_sum, h_wave]

/-- Suppose `V` fits `S` (the hypothesis `h`), so that `h.realHomeomorph` gives each point of
`GInf E ε = ∏_v U(diag ε)` a component in the complex unitary group `G₁` at each infinite place `v`.
The kernel `typeKernel l ε` is the product over `v` of the formal degree times the conjugate
coefficient of the discrete series of doubled Harish-Chandra parameter `l v`. Its conjugate at
`g⁻¹ y` is the product of the formal degrees times the product of `(l v).dsCoeffInFrame` at
`g_v⁻¹ y_v`, where `g_v` and `y_v` are the components of `g` and `y`, and `dsCoeffInFrame` is the
coefficient carried from `U(diag ε)` to `G₁` by the fixed unitary matrix `UnitarySignFrame 𝔰 ε`. -/
lemma conj_typeKernel (h : S.Fits V l kw Y η) (g y : GInf E ε) :
    conj (typeKernel l ε (g⁻¹ * y)) = (∏ v : InfinitePlace E, ((l v).formalDegree : ℂ)) *
      ∏ v : InfinitePlace E, (l v).dsCoeffInFrame
        ((h.realHomeomorph g v)⁻¹ * h.realHomeomorph y v) := by
  rw [map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h_frame : frameEquiv ((h.realHomeomorph g v)⁻¹ * h.realHomeomorph y v) = (g⁻¹ * y) v := by
    -- `realHomeomorph` is the inverse frame followed by left multiplication by some `k` at each
    -- place.
    obtain ⟨k, hk⟩ : ∃ k : 𝔰.G₁, ∀ z : GInf E ε, h.realHomeomorph z v = k * frameEquiv.symm (z v) :=
      ⟨_, fun _ ↦ rfl⟩
    simp [hk, mul_assoc]
  simp [HCParam.dsCoeffInFrame, h_frame, HCParam.dsKernel]

/-- Suppose `V` fits `S` (the hypothesis `h`); in particular the Bessel system `S.besselSystem v` at
`v` has weight `kw v`. Let `ζ` be a vector of the Weyl module of weight `kw`, in the basis indexed
by `WeylIndex 𝔰.κ kw`. A point `a` of `GInf E 1`, the product over `v` of the compact unitary group
`U(κ)` on the index set `𝔰.κ`, acts on `ζ` by `conjWeylRep kw 0 a`, the Schur matrix of the complex
conjugate of `a`; the argument `0` is the exponent of the determinant twist. In the coordinates
`weylBesselEquiv` this action is the transpose of the Kronecker product `kroneckerPi` of the unitary
matrices `(S.besselSystem v).rep` by which `a⁻¹` acts on the values of the local Bessel
functions. -/
lemma weylBesselEquiv_conjWeylRep (h : S.Fits V l kw Y η) (a : GInf E (1 : 𝔰.κ → ℤˣ))
    (ζ : WeylIndex 𝔰.κ kw → ℂ) :
    h.weylBesselEquiv (conjWeylRep kw 0 a ζ) = h.weylBesselEquiv ζ ᵥ*
      kroneckerPi fun v : InfinitePlace E ↦
        ((S.besselSystem v).rep (unitSignEquiv 𝔰.κ (a v))⁻¹).val := by
  have h_transpose (v : InfinitePlace E) :
      (unitSignEquiv 𝔰.κ (a v))⁻¹.val.valᵀ = (a v).val.val.map (starRingEnd ℂ) := by
    rw [← map_inv, coe_unitSignEquiv, ← coe_map_conj_inv_eq_transpose, Subgroup.coe_inv, inv_inv,
      GeneralLinearGroup.val_map_apply]
  simp only [weylBesselEquiv_vecMul, h_transpose]
  simp [conjWeylRep, weylRep]

/-- If `V` fits `S`, the product over the infinite places `v` of the formal degrees of the discrete
series of parameters `l v` is not zero. -/
lemma prod_formalDegree_ne_zero (h : S.Fits V l kw Y η) :
    ∏ v : InfinitePlace E, ((l v).formalDegree : ℂ) ≠ 0 := by
  -- It is a factor of the conjugate of the value at one of the idempotent kernel.
  intro h_zero
  apply h.isIdempotentKernel.apply_one_ne_zero
  simpa only [h_zero, zero_mul, inv_mul_cancel, map_eq_zero] using h.conj_typeKernel 1 1

/-- Suppose `V` with grading `Y` fits `S` (the hypothesis `h`). Let `g`, `y` be points of
`GInf E ε = ∏_v U(diag ε)`, carried to `∏_v G₁` by `realHomeomorph`, and let `u v` be a vector of
the value space `ℂ^I` of the Bessel system at `v`, on which `U(κ)` acts by `rep`. The local
integrand `besselIntegrand l rep x u y` at `(r, a)` in the local Bessel group is
`l.dsCoeffInFrame (x⁻¹ r y) • wave (-simpleRootSum r) • rep a⁻¹ u`. Let `s` be a real point of the
Bessel group of `Y`; its components `besselRealToPi s v` are made with `realCoords`, and
`realCoords s * realHomeomorph y = realHomeomorph (s * y)`. At these components the tensor product
of the integrands, in coordinates `S.BesselCoord`, is the product of the coefficients at
`(realHomeomorph g)⁻¹ * realHomeomorph (s * y)`, times the inverse of `besselChar` at `s`, times the
tensor product of the `u v` moved by the Kronecker product `kroneckerPi` of the matrices `rep` of
the inverse of the Levi part of `s`. -/
lemma prod_besselIntegrand (h : S.Fits V l kw Y η) (g y : GInf E ε)
    (u : ∀ v : InfinitePlace E, EuclideanSpace ℂ (S.besselSystem v).Index) (s : Y.besselReal) :
    (fun i : S.BesselCoord ↦ ∏ v : InfinitePlace E,
      besselIntegrand (l v) (S.besselSystem v).rep (h.realHomeomorph g v) (u v)
        (h.realHomeomorph y v) (h.besselRealToPi s v) (i v)) =
      (∏ v : InfinitePlace E,
          (l v).dsCoeffInFrame ((h.realHomeomorph g v)⁻¹ * h.realHomeomorph (s * y) v)) •
        (h.besselChar (s.val, 1))⁻¹ • (kroneckerPi fun v : InfinitePlace E ↦ ((S.besselSystem v).rep
          (unitSignEquiv 𝔰.κ ((Y.leviPart ⟨(s.val, 1), s.property⟩).fst v))⁻¹).val) *ᵥ
          fun i : S.BesselCoord ↦ ∏ v : InfinitePlace E, u v (i v) := by
  ext i
  simp only [Pi.smul_apply, besselChar_inl_inv, ← realCoords_mul_realHomeomorph,
    kroneckerPi_mulVec_prod _ fun v ↦ (u v).ofLp, smul_eq_mul, ← Finset.prod_mul_distrib]
  -- Factor by factor this is the definition of `besselIntegrand`.
  rfl

/-- **The Bessel function as one integral.** Let `E` be a CM field, fix a unitary matrix that
carries the form of `G₁` to the diagonal form of signs `ε`, and suppose the hermitian space `V` with
grading `Y` and central element `η` fits the filling data `S`; in particular the Bessel system of
`S` at `v` has type `(l v, kw v)`. There are a point `g` of `GInf E ε = ∏_v U(diag ε)` and a linear
form `t` on the Weyl module of weight `kw`, whose basis is indexed by `WeylIndex 𝔰.κ kw`, with the
following property. Evaluate the tensor product `S.besselFn .full` of the local Bessel functions
(not their cuts) at a point `y`, carried to `∏_v G₁` by `realHomeomorph`, and pair it with a vector
`ζ` of the Weyl module, carried to the dual of the values of the Bessel function by
`weylBesselEquiv`. The result is the integral of `conj (typeKernel l ε (g⁻¹ s y)) (besselChar s)⁻¹
t(a ζ)` over `s = n a` in `Y.besselReal`, the real points of the Bessel group `R = U ⋊ H` of `Y`,
against the Haar measure `haar`, whose normalisation is absorbed in `t`. -/
theorem exists_besselFn_eq_integral (h : S.Fits V l kw Y η) :
    ∃ (g : GInf E ε) (t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ),
      ∀ (y : GInf E ε) (ζ : WeylIndex 𝔰.κ kw → ℂ),
        h.weylBesselEquiv ζ ⬝ᵥ S.besselFn .full (h.realHomeomorph y) =
          ∫ s : Y.besselReal, conj (typeKernel l ε (g⁻¹ * s.val * y)) *
            ((h.besselChar (s.val, 1))⁻¹ *
              t (conjWeylRep kw 0 (Y.leviPart ⟨(s.val, 1), s.property⟩).fst ζ)) ∂haar := by
  -- Take the point with components `x v` and pair with the tensor product of the vectors `u v`;
  -- the constants `a v`, the formal degrees and the ratio `c` of the Haar measures go into `t`.
  have h_avg (v : InfinitePlace E) :
      ∃ (a : ℝ) (x : 𝔰.G₁) (u : EuclideanSpace ℂ (S.besselSystem v).Index), ∀ y : 𝔰.G₁,
        Integrable (besselIntegrand (l v) (S.besselSystem v).rep x u y) 𝔰.besselGraphMeasure ∧
          (S.besselSystem v).besselFn .full y =
            a • besselAverage (l v) (S.besselSystem v).rep x u y :=
    (h.isDiscreteSeriesBessel v).exists_eq_besselAverage
  choose a x u h_int h_eq using h_avg
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ F : (InfinitePlace E → 𝔰.besselGraph) → ℂ,
      ∫ q, F q ∂(Measure.pi fun _ : InfinitePlace E ↦ 𝔰.besselGraphMeasure) =
        c * ∫ s : Y.besselReal, F (h.besselRealToPi s) ∂haar :=
    h.exists_integral_pi_eq
  obtain ⟨g, rfl⟩ : ∃ g : GInf E ε, h.realHomeomorph g = x := h.realHomeomorph.surjective x
  let w : S.BesselCoord → ℂ := fun i ↦ ∏ v, u v (i v)
  let C : ℂ := (∏ v, (a v : ℂ)) * c / ∏ v, ((l v).formalDegree : ℂ)
  let t : (WeylIndex 𝔰.κ kw → ℂ) →ₗ[ℂ] ℂ :=
    C • (dotProductBilin ℂ ℂ).flip w ∘ₗ h.weylBesselEquiv.toLinearMap
  refine ⟨g, t, fun y ζ ↦ ?_⟩
  let f (v : InfinitePlace E) : 𝔰.besselGraph → EuclideanSpace ℂ (S.besselSystem v).Index :=
    besselIntegrand (l v) (S.besselSystem v).rep (h.realHomeomorph g v) (u v) (h.realHomeomorph y v)
  have h_prod (s : Y.besselReal) :
      (fun i : S.BesselCoord ↦ ∏ v, f v (h.besselRealToPi s v) (i v)) =
        (∏ v, (l v).dsCoeffInFrame ((h.realHomeomorph g v)⁻¹ * h.realHomeomorph (s * y) v)) •
          (h.besselChar (s.1, 1))⁻¹ • (kroneckerPi fun v ↦ ((S.besselSystem v).rep
            (unitSignEquiv 𝔰.κ ((Y.leviPart ⟨(s.1, 1), s.2⟩).1 v))⁻¹).1) *ᵥ w :=
    h.prod_besselIntegrand g y u s
  have h_besselFn : S.besselFn .full (h.realHomeomorph y) = (∏ v, (a v : ℂ)) •
      fun i ↦ ∏ v, (∫ s, f v s ∂𝔰.besselGraphMeasure) (i v) := by
    simp [funext_iff, Filling.besselFn, f, h_eq, besselAverage, Finset.prod_mul_distrib]
  have ht (ξ : WeylIndex 𝔰.κ kw → ℂ) : t ξ = C * h.weylBesselEquiv ξ ⬝ᵥ w := rfl
  calc _ = (∏ v, (a v : ℂ)) * c * ∫ s : Y.besselReal,
          h.weylBesselEquiv ζ ⬝ᵥ fun i ↦ ∏ v, f v (h.besselRealToPi s v) (i v) ∂haar := by
        rw [h_besselFn, dotProduct_smul, dotProduct_prod_integral _ fun v ↦ h_int v _, hc,
          smul_eq_mul, mul_assoc]
    _ = _ := by
        -- Compare the integrands at `s` by the factorization `h_prod`.
        rw [← integral_const_mul]
        refine integral_congr_ae (.of_forall fun s ↦ ?_)
        simp only [h_prod, mul_assoc g⁻¹, h.conj_typeKernel, ht, C, weylBesselEquiv_conjWeylRep,
          dotProduct_smul, dotProduct_mulVec, smul_eq_mul]
        field_simp [h.prod_formalDegree_ne_zero]

end Filling.Fits

end New

end
