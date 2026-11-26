import Lib.DiscreteSeries.Haar.CayleyChart

/-!
# Coordinates for the Gram map

Let `J` be a hermitian matrix. The Gram map sends a tuple of vectors, the columns of a complex
matrix `Y`, to the hermitian matrix `T = Yᴴ J Y`. Tuples carry Lebesgue measure `dY`, and hermitian
matrices the product `dT` of the Lebesgue measures of the entries on and above the diagonal.

* `New.joinCols`, `New.joinCol`: joining two groups of columns into one matrix; this preserves
  volume (`New.measurePreserving_joinCols`, `New.measurePreserving_joinCol`).
* `New.hermOfReal`, `New.gramCoords`: real coordinates on hermitian matrices, and the Gram map in
  these coordinates.
* `New.lintegral_eq_skewOfReal_add_hermOfReal`: Lebesgue measure on matrices `Z = S + T / 2` of size
  `n`, with `S` skew-hermitian and `T` hermitian, is `2 ^ (-n) dS dT`.
* `New.exists_measurePreserving_hermBlocks`, `New.exists_measurePreserving_hermCorner`: cutting a
  hermitian matrix into the corresponding blocks preserves volume.

Notions from other files:
* `New.skewOfReal`: the skew-hermitian matrix with given real coordinates, normalised so that
  Lebesgue measure in the coordinates is that of the entries on and above the diagonal.
* `New.skewCoords`: the real-linear left inverse of `New.skewOfReal`, inverse to it on
  skew-hermitian matrices.
-/

noncomputable section

namespace New

open Matrix MeasureTheory Measure Complex Fintype ENNReal Norms.L2Operator Filter Topology

variable {ι n n₁ n₂ : Type}

/-! ### Columns and transposes -/

/-- The linear isomorphism that sends a pair of matrices to the matrix with the columns of both, in
the places given by `e`. -/
def joinCols (e : n₁ ⊕ n₂ ≃ n) : (Matrix ι n₁ ℂ × Matrix ι n₂ ℂ) ≃ₗ[ℝ] Matrix ι n ℂ where
  toFun p := (fromCols p.1 p.2).submatrix id e.symm
  invFun Y := (Y.submatrix id (e ∘ Sum.inl), Y.submatrix id (e ∘ Sum.inr))
  map_add' := by simp [← ext_iff, e.surjective.forall]
  map_smul' := by simp [← ext_iff, e.surjective.forall]
  left_inv := by simp [Function.LeftInverse, Prod.ext_iff, ← ext_iff]
  right_inv := by simp [Function.RightInverse, Function.LeftInverse, ← ext_iff, e.surjective.forall]

/-- Joining two groups of columns is continuous. -/
@[fun_prop]
theorem continuous_joinCols [Fintype ι] [Fintype n₁] [Fintype n₂] (e : n₁ ⊕ n₂ ≃ n) :
    Continuous (joinCols (ι := ι) e) := (joinCols e).continuous_of_finiteDimensional

/-- Joining two groups of complex columns (`joinCols`) preserves Lebesgue measure. -/
theorem measurePreserving_joinCols [Fintype ι] [Fintype n] [Fintype n₁] [Fintype n₂]
    (e : n₁ ⊕ n₂ ≃ n) : MeasurePreserving (joinCols (ι := ι) e) := by
  classical
  have h_norm (p : Matrix ι n₁ ℂ × Matrix ι n₂ ℂ) :
      ∑ a : ι, ∑ b : n, ‖joinCols e p a b‖ ^ 2 =
        ∑ a : ι, ∑ b : n₁, ‖p.1 a b‖ ^ 2 + ∑ a : ι, ∑ b : n₂, ‖p.2 a b‖ ^ 2 := by
    simp [joinCols, ← e.sum_comp, Finset.sum_add_distrib]
  have : IsAddHaarMeasure (volume : Measure (Matrix ι n₁ ℂ × Matrix ι n₂ ℂ)) :=
    prod.instIsAddHaarMeasure _ _
  exact HasGaussianIntegral.measurePreserving _ h_norm

/-- Placing one complex matrix above another preserves Lebesgue measure. -/
theorem measurePreserving_fromRows {l m k : Type} [Fintype l] [Fintype m] [Fintype k] :
    MeasurePreserving fun p : Matrix l k ℂ × Matrix m k ℂ ↦ fromRows p.1 p.2 :=
  volume_measurePreserving_sumPiEquivProdPi_symm fun _ ↦ k → ℂ

/-- Left multiplication by a matrix acts on each of two groups of columns separately. -/
theorem mul_joinCols {l : Type} [Fintype ι] (e : n₁ ⊕ n₂ ≃ n) (A : Matrix l ι ℂ)
    (x : Matrix ι n₁ ℂ) (y : Matrix ι n₂ ℂ) :
    A * joinCols e (x, y) = joinCols e (A * x, A * y) := by
  simp [← ext_iff, e.surjective.forall, joinCols, mul_apply]

/-- A vector as a matrix with one column. -/
def toCol (κ R : Type) [TopologicalSpace R] : (κ → R) ≃ₜ Matrix κ Unit R :=
  .piCongrRight fun _ ↦ (Homeomorph.funUnique Unit R).symm

@[simp]
theorem toCol_apply {κ R : Type} [TopologicalSpace R] (v : κ → R) (i : κ) (u : Unit) :
    toCol κ R v i u = v i := rfl

/-- Reading a vector as a matrix with one column (`toCol`) preserves volume. -/
theorem measurePreserving_toCol (κ R : Type) [Fintype κ] [TopologicalSpace R] [MeasureSpace R]
    [SigmaFinite (volume : Measure R)] : MeasurePreserving (toCol κ R) :=
  volume_preserving_pi fun _ ↦ (volume_preserving_funUnique Unit R).symm

/-- A vector and a real number as a one-column matrix and a one-by-one matrix. -/
def toCorner (κ : Type) : ((κ → ℂ) × ℝ) ≃ₜ Matrix κ Unit ℂ × Matrix Unit Unit ℝ :=
  (toCol κ ℂ).prodCongr ((Homeomorph.funUnique Unit ℝ).symm.trans (toCol Unit ℝ))

theorem toCorner_apply {κ : Type} (v : κ → ℂ) (r : ℝ) :
    toCorner κ (v, r) = (toCol κ ℂ v, toCol Unit ℝ fun _ : Unit ↦ r) := rfl

theorem measurePreserving_toCorner [Fintype n] : MeasurePreserving (toCorner n) :=
  (measurePreserving_toCol n ℂ).prod
    ((measurePreserving_toCol Unit ℝ).comp (volume_preserving_funUnique Unit ℝ).symm)

/-- The matrix whose columns are those of `p.1` and the vector `p.2`, in the places given by `e`. -/
def joinCol (e : n₁ ⊕ Unit ≃ n) (p : Matrix ι n₁ ℂ × (ι → ℂ)) : Matrix ι n ℂ :=
  joinCols e (p.1, toCol ι ℂ p.2)

@[simp]
theorem joinCol_inl (e : n₁ ⊕ Unit ≃ n) (p : Matrix ι n₁ ℂ × (ι → ℂ)) (i : ι) (a : n₁) :
    joinCol e p i (e (.inl a)) = p.1 i a := by simp [joinCol, joinCols]

@[simp]
theorem joinCol_inr (e : n₁ ⊕ Unit ≃ n) (p : Matrix ι n₁ ℂ × (ι → ℂ)) (i : ι) :
    joinCol e p i (e (.inr ())) = p.2 i := by simp [joinCol, joinCols]

@[fun_prop]
theorem continuous_joinCol [Fintype ι] [Fintype n₁] (e : n₁ ⊕ Unit ≃ n) :
    Continuous (joinCol (ι := ι) e) := (continuous_joinCols e).comp (by fun_prop)

/-- Adjoining a complex vector as a further column (`joinCol`) preserves Lebesgue measure. -/
theorem measurePreserving_joinCol [Fintype ι] [Fintype n] [Fintype n₁] (e : n₁ ⊕ Unit ≃ n) :
    MeasurePreserving (joinCol (ι := ι) e) :=
  (measurePreserving_joinCols e).comp ((MeasurePreserving.id _).prod (measurePreserving_toCol ι ℂ))

theorem mul_toCol {l : Type} [Fintype ι] (A : Matrix l ι ℂ) (v : ι → ℂ) :
    A * toCol ι ℂ v = toCol l ℂ (A *ᵥ v) := rfl

/-- Left multiplication by a matrix acts separately on the given columns and on the adjoined
one. -/
theorem mul_joinCol {l : Type} [Fintype ι] (e : n₁ ⊕ Unit ≃ n) (A : Matrix l ι ℂ)
    (Y : Matrix ι n₁ ℂ) (v : ι → ℂ) : A * joinCol e (Y, v) = joinCol e (A * Y, A *ᵥ v) := by
  simp only [joinCol, mul_joinCols, mul_toCol]

/-- The inverse of `toCorner` reads off the column and the single entry of the corner. -/
theorem toCorner_symm_apply {κ : Type} (B : Matrix κ Unit ℂ) (D : Matrix Unit Unit ℝ) :
    (toCorner κ).symm (B, D) = (fun a : κ ↦ B a (), D () ()) := rfl

/-- On the matrices without columns, which form a single point, the volume is the unit mass. -/
theorem volume_eq_dirac_of_isEmpty [Fintype ι] [Fintype n] {R : Type} [MeasureSpace R]
    [SigmaFinite (volume : Measure R)] [IsEmpty n] (Y : Matrix ι n R) : volume = dirac Y := by
  refine ext_iff_singleton.2 fun Z ↦ ?_
  rw [Subsingleton.eq_univ_of_nonempty (Set.singleton_nonempty Z), measure_univ (μ := dirac Y)]
  exact (pi_univ _).trans (Finset.prod_eq_one fun _ _ ↦ pi_empty_univ _)

/-- The conjugate transpose preserves Lebesgue measure on complex matrices. -/
theorem measurePreserving_conjTranspose [Fintype ι] [Fintype n] [DecidableEq ι] [DecidableEq n] :
    MeasurePreserving fun b : Matrix ι n ℂ ↦ bᴴ := by
  have h_norm (b : Matrix ι n ℂ) :
      ∑ a : n, ∑ i : ι, ‖bᴴ a i‖ ^ 2 = ∑ i : ι, ∑ a : n, ‖b i a‖ ^ 2 := by
    simpa using Finset.sum_comm
  let e : Matrix ι n ℂ ≃ₗ[ℝ] Matrix n ι ℂ :=
    { conjTransposeAddEquiv ι n ℂ with map_smul' := by simp [star_trivial] }
  exact HasGaussianIntegral.measurePreserving e h_norm

section Hermitian

variable [Fintype ι] [DecidableEq n]

/-! ### Measurability and linear changes of variables -/

/-- The product of two measurable families of complex matrices is measurable. -/
@[fun_prop]
theorem _root_.Measurable.matrix_mul [Fintype n] {X : Type} [MeasurableSpace X] [Fintype n₁]
    {A : X → Matrix ι n₁ ℂ} {B : X → Matrix n₁ n ℂ} (hA : Measurable A) (hB : Measurable B) :
    Measurable fun x : X ↦ A x * B x :=
  (continuous_fst.matrix_mul continuous_snd).measurable.comp (hA.prodMk hB)

@[fun_prop]
theorem measurable_matrix_det [Fintype n] : Measurable fun Z : Matrix n n ℂ ↦ Z.det :=
  continuous_id.matrix_det.measurable

@[fun_prop]
theorem measurable_matrix_inv [Fintype n] : Measurable fun Z : Matrix n n ℂ ↦ Z⁻¹ := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']
  fun_prop

/-- Substitution by an invertible real linear map `T` in an integral against an additive Haar
measure: the Jacobian is `|det T|`. -/
theorem lintegral_eq_abs_det_mul_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] {T : V →ₗ[ℝ] V} (hT : T.det ≠ 0) {K : V → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ y : V, K y ∂μ = ENNReal.ofReal |T.det| * ∫⁻ y : V, K (T y) ∂μ := by
  have h_map : ∫⁻ y : V, K (T y) ∂μ = ENNReal.ofReal |T.det⁻¹| * ∫⁻ y : V, K y ∂μ := by
    rw [← lintegral_map hK T.continuous_of_finiteDimensional.measurable,
      map_linearMap_addHaar_eq_smul_addHaar μ hT, lintegral_smul_measure, smul_eq_mul]
  rw [h_map, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul, mul_inv_cancel₀ hT]
  simp

/-- Substitution `y ↦ P y Q` in an integral over complex matrices, for invertible `P` and `Q`: the
Jacobian is `|det P| ^ (2 |n|) |det Q| ^ (2 |ι|)`. -/
theorem lintegral_eq_det_mul_comp_mul_mul [Fintype n]
    [DecidableEq ι] {P : Matrix ι ι ℂ} {Q : Matrix n n ℂ}
    (hP : P.det ≠ 0) (hQ : Q.det ≠ 0) {K : Matrix ι n ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ y : Matrix ι n ℂ, K y =
      ‖P.det‖ₑ ^ (2 * card n) * ‖Q.det‖ₑ ^ (2 * card ι) * ∫⁻ y : Matrix ι n ℂ, K (P * y * Q) := by
  let L : Matrix ι n ℂ →ₗ[ℝ] Matrix ι n ℂ := mulRightLinearMap ι ℝ Q ∘ₗ mulLeftLinearMap n ℝ P
  have h_det : L.det = ‖P.det‖ ^ (2 * card n) * ‖Q.det‖ ^ (2 * card ι) :=
    det_mulLeft_mulRight_real P Q
  have h_ne : L.det ≠ 0 := h_det.trans_ne (by positivity)
  simp [lintegral_eq_abs_det_mul_comp volume h_ne hK, h_det, L, ENNReal.ofReal_mul,
    ENNReal.ofReal_pow]

/-! ### Hermitian coordinates -/

/-- The hermitian matrix with real coordinates `t`: it is `-i` times the skew-hermitian matrix
`skewOfReal t`, so its diagonal entries are those of `t`. Lebesgue measure in `t` is the product
of the Lebesgue measures of the entries on and above the diagonal. -/
def hermOfReal (t : Matrix n n ℝ) : Matrix n n ℂ := -I • skewOfReal t

/-- The Gram map: the real coordinates, in the sense of `hermOfReal`, of the Gram matrix
`Yᴴ J Y` of the columns of `Y`, for a hermitian `J` (`hermOfReal_gramCoords`). -/
def gramCoords (J : Matrix ι ι ℂ) (Y : Matrix ι n ℂ) : Matrix n n ℝ :=
  skewCoords (I • (Yᴴ * J * Y))

@[simp]
theorem conjTranspose_hermOfReal (t : Matrix n n ℝ) : (hermOfReal t)ᴴ = hermOfReal t := by
  simp [hermOfReal, conjTranspose_smul]

@[simp]
theorem skewCoords_I_smul_hermOfReal (t : Matrix n n ℝ) : skewCoords (I • hermOfReal t) = t := by
  simp [hermOfReal, smul_smul]

/-- For a hermitian `J`, the hermitian matrix with the real coordinates `gramCoords J Y` is the
Gram matrix `Yᴴ J Y`. -/
theorem hermOfReal_gramCoords {J : Matrix ι ι ℂ} (hJ : J.IsHermitian) (Y : Matrix ι n ℂ) :
    hermOfReal (gramCoords J Y) = Yᴴ * J * Y := by
  have h_skew : (I • (Yᴴ * J * Y))ᴴ = -(I • (Yᴴ * J * Y)) := by
    simp [conjTranspose_smul, hJ.eq, Matrix.mul_assoc]
  simp [hermOfReal, gramCoords, skewOfReal_skewCoords h_skew, smul_smul]

@[fun_prop]
theorem continuous_gramCoords [Fintype n] (J : Matrix ι ι ℂ) :
    Continuous (gramCoords J : Matrix ι n ℂ → Matrix n n ℝ) :=
  skewCoords.continuous_of_finiteDimensional.comp (by fun_prop)

@[fun_prop]
theorem continuous_hermOfReal [Fintype n] : Continuous (hermOfReal : Matrix n n ℝ → Matrix n n ℂ) :=
  skewOfReal.continuous_of_finiteDimensional.const_smul (-I)

/-- In the real coordinates `t` of hermitian matrices `T = hermOfReal t` of size `n`, the congruence
`T ↦ Cᴴ T C` has the Jacobian `|det C| ^ (2 n)`. -/
theorem lintegral_eq_det_mul_comp_congruence [Fintype n] {C : Matrix n n ℂ} (hC : C.det ≠ 0)
    {G : Matrix n n ℂ → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ t : Matrix n n ℝ, G (hermOfReal t) =
      ‖C.det‖ₑ ^ (2 * card n) * ∫⁻ t : Matrix n n ℝ, G (Cᴴ * hermOfReal t * C) := by
  let L : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    skewCoords ∘ₗ LinearMap.mulLeftRight ℝ (Cᴴ, C) ∘ₗ skewOfReal
  -- `abs_det_skew_congruence` allows coordinate changes on both sides; here both are trivial.
  have h_det : |L.det| = ‖C.det‖ ^ (2 * card n) := by
    simpa using abs_det_skew_congruence (LinearEquiv.refl ℝ (Matrix n n ℝ)) C LinearMap.id
  have h_herm (t : Matrix n n ℝ) : hermOfReal (L t) = Cᴴ * hermOfReal t * C := by
    simp [L, hermOfReal, skewOfReal_skewCoords, Matrix.mul_assoc]
  have h_ne : L.det ≠ 0 := abs_ne_zero.1 (h_det.trans_ne (by positivity))
  simp [lintegral_eq_abs_det_mul_comp volume h_ne (show Measurable fun t ↦ G (hermOfReal t) by
    fun_prop), h_det, h_herm, ENNReal.ofReal_pow]

/-- The derivative of the Gram matrix `σᴴ J σ` of a differentiable family `σ` of matrices is
`σᴴ J dσ + dσᴴ J σ`, read in the coordinates of `gramCoords`. -/
theorem hasFDerivAt_gramCoords {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [DecidableEq ι] (J : Matrix ι ι ℂ) {σ : V → Matrix ι ι ℂ} {σ' : V →L[ℝ] Matrix ι ι ℂ} {t : V}
    (hσ : HasFDerivAt σ σ' t) : ∃ D : V →L[ℝ] Matrix ι ι ℝ,
      HasFDerivAt (fun x : V ↦ gramCoords J (σ x)) D t ∧
      ∀ v : V, D v = skewCoords (I • ((σ t)ᴴ * J * σ' v + (σ' v)ᴴ * J * σ t)) :=
  -- the product rule, followed by the linear map `skewCoords`
  ⟨_, skewCoords.toContinuousLinearMap.hasFDerivAt.comp t
    (((hσ.star.mul_const' J).mul' hσ).const_smul I), fun _ ↦ rfl⟩

/-- The Gram map `Y ↦ Yᴴ J Y` on square matrices, read in the real coordinates of
`gramCoords`, is continuously differentiable. -/
theorem contDiff_gramCoords [DecidableEq ι] (J : Matrix ι ι ℂ) :
    ContDiff ℝ 1 (gramCoords J : Matrix ι ι ℂ → Matrix ι ι ℝ) := by
  have h_star : ContDiff ℝ 1 fun Y : Matrix ι ι ℂ ↦ Yᴴ := (starL' ℝ).contDiff
  exact skewCoords.toContinuousLinearMap.contDiff.comp
    (((h_star.mul contDiff_const).mul contDiff_id).const_smul I)

/-- The isomorphism `(t, s) ↦ S + T / 2` onto the complex matrices, where `S` is the skew-hermitian
matrix with coordinates `s` and `T` the hermitian matrix with coordinates `t`. The inverse reads
`T = Z + Zᴴ` and `S = (Z - Zᴴ) / 2`. -/
def skewAddHerm : (Matrix n n ℝ × Matrix n n ℝ) ≃ₗ[ℝ] Matrix n n ℂ where
  toFun p := skewOfReal p.2 + (2⁻¹ : ℂ) • hermOfReal p.1
  invFun Z := (skewCoords (I • (Z + Zᴴ)), skewCoords ((2⁻¹ : ℂ) • (Z - Zᴴ)))
  map_add' p q := by simp [hermOfReal, smul_add, add_add_add_comm]
  map_smul' c p := by simp [hermOfReal, smul_comm c]
  left_inv p := by
    have hZ : (skewOfReal p.2 + (2⁻¹ : ℂ) • hermOfReal p.1)ᴴ =
        -skewOfReal p.2 + (2⁻¹ : ℂ) • hermOfReal p.1 := by simp [conjTranspose_smul]
    refine Prod.ext ((congrArg skewCoords ?_).trans (skewCoords_I_smul_hermOfReal p.1))
      ((congrArg skewCoords ?_).trans (skewCoords_skewOfReal p.2))
    all_goals
      rw [hZ]
      module
  right_inv Z := by
    have h_herm : (I • (Z + Zᴴ))ᴴ = -(I • (Z + Zᴴ)) := by simp [conjTranspose_smul, add_comm]
    have h_skew : ((2⁻¹ : ℂ) • (Z - Zᴴ))ᴴ = -((2⁻¹ : ℂ) • (Z - Zᴴ)) := by
      simp [conjTranspose_smul, ← smul_neg]
    change skewOfReal (skewCoords ((2⁻¹ : ℂ) • (Z - Zᴴ))) +
      (2⁻¹ : ℂ) • hermOfReal (skewCoords (I • (Z + Zᴴ))) = Z
    simp only [hermOfReal, skewOfReal_skewCoords h_herm, skewOfReal_skewCoords h_skew,
      smul_smul (-I), neg_mul, I_mul_I, neg_neg, one_smul]
    module

theorem skewAddHerm_apply (t s : Matrix n n ℝ) :
    skewAddHerm (t, s) = skewOfReal s + (2⁻¹ : ℂ) • hermOfReal t := rfl

theorem skewAddHerm_symm_apply (Z : Matrix n n ℂ) :
    skewAddHerm.symm Z = (skewCoords (I • (Z + Zᴴ)), skewCoords ((2⁻¹ : ℂ) • (Z - Zᴴ))) := rfl

omit [DecidableEq n] in
/-- Scaling the entries of a real matrix by numbers `c a b` is a linear map with determinant
`∏ c a b`. -/
theorem exists_linearMap_scale_entries [Fintype n] (c : n → n → ℝ) :
    ∃ T : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ,
      (∀ (y : Matrix n n ℝ) (a b : n), T y a b = c a b * y a b) ∧
      T.det = ∏ a : n, ∏ b : n, c a b := by
  let L (a : n) : (n → ℝ) →ₗ[ℝ] n → ℝ :=
    LinearMap.pi fun b : n ↦ (c a b • LinearMap.id) ∘ₗ LinearMap.proj b
  refine ⟨LinearMap.pi fun a : n ↦ L a ∘ₗ LinearMap.proj a,
    fun y a b ↦ rfl, (LinearMap.det_pi _).trans ?_⟩
  simp [L, LinearMap.det_pi]

/-- The squared norms of the entries of `skewAddHerm (t', s')` in terms of `t` and `s`, when `t'`
and `s'` are `t` and `s` multiplied by `2 / d` and `1 / d` entrywise, with `d = 1` on the diagonal
and `d = √2` off it. -/
theorem norm_sq_skewAddHerm_of_scale {t s t' s' : Matrix n n ℝ}
    (ht : ∀ a b : n, t' a b = 2 / (if a = b then 1 else √2) * t a b)
    (hs : ∀ a b : n, s' a b = 1 / (if a = b then 1 else √2) * s a b) (a b : n) :
    ‖skewAddHerm (t', s') a b‖ ^ 2 = ((t a b + t b a + s a b - s b a) ^ 2 +
      (s a b + s b a + t b a - t a b) ^ 2) / 4 := by
  obtain rfl | hab := eq_or_ne a b
  · simp [skewAddHerm_apply, ht, hs, hermOfReal, skewOfReal, Complex.sq_norm, normSq_apply]
    ring
  · simp [skewAddHerm_apply, ht, hs, hermOfReal, skewOfReal, Complex.sq_norm, normSq_apply, hab,
      hab.symm, field]
    ring

variable [Fintype n]

/-- The isomorphism `skewAddHerm`, `(t, s) ↦ S + T / 2`, onto the complex matrices of size `n`
has Jacobian `2 ^ (-n)`; here `S` is the skew-hermitian matrix with coordinates `s` and `T` the
hermitian one with coordinates `t`. -/
theorem lintegral_eq_comp_skewAddHerm {K : Matrix n n ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Z : Matrix n n ℂ, K Z =
      (2 ^ card n)⁻¹ * ∫⁻ p : Matrix n n ℝ × Matrix n n ℝ, K (skewAddHerm p) := by
  -- After scaling the entries of `t` by `2 / d` and those of `s` by `1 / d`, with `d = 1` on the
  -- diagonal and `d = √2` off it, the map is an isometry for the sums of squares of the entries.
  let d (a b : n) : ℝ := if a = b then 1 else √2
  obtain ⟨T₁, hT₁, hT₁_det⟩ := exists_linearMap_scale_entries fun a b : n ↦ 2 / d a b
  obtain ⟨T₂, hT₂, hT₂_det⟩ := exists_linearMap_scale_entries fun a b : n ↦ 1 / d a b
  have h_det : (T₁.prodMap T₂).det = 2 ^ card n := by
    have h_entry (a b : n) : 2 / d a b * (1 / d a b) = if a = b then 2 else 1 := by
      by_cases hab : a = b <;> simp [d, hab, field]
    simp only [LinearMap.det_prodMap, hT₁_det, hT₂_det, ← Finset.prod_mul_distrib, h_entry]
    simp
  have h_ne : (T₁.prodMap T₂).det ≠ 0 := h_det.trans_ne (by positivity)
  have h_iso : MeasurePreserving (((T₁.prodMap T₂).equivOfDetNeZero h_ne).trans skewAddHerm) := by
    refine HasGaussianIntegral.measurePreserving _ fun p ↦ ?_
    let Z : Matrix n n ℂ := skewAddHerm (T₁ p.1, T₂ p.2)
    have h_sq (a b : n) : ‖Z a b‖ ^ 2 + ‖Z b a‖ ^ 2 =
        p.1 a b ^ 2 + p.2 a b ^ 2 + (p.1 b a ^ 2 + p.2 b a ^ 2) := by
      rw [norm_sq_skewAddHerm_of_scale (hT₁ p.1) (hT₂ p.2),
        norm_sq_skewAddHerm_of_scale (hT₁ p.1) (hT₂ p.2)]
      ring
    -- Sum over all `a`, `b`: each entry is counted twice on both sides.
    have h_sum : ∑ a : n, ∑ b : n, (‖Z a b‖ ^ 2 + ‖Z b a‖ ^ 2) =
        ∑ a : n, ∑ b : n, (p.1 a b ^ 2 + p.2 a b ^ 2 + (p.1 b a ^ 2 + p.2 b a ^ 2)) := by
      simp only [h_sq]
    change ∑ a : n, ∑ b : n, ‖Z a b‖ ^ 2 =
      ∑ a : n, ∑ b : n, p.1 a b ^ 2 + ∑ a : n, ∑ b : n, p.2 a b ^ 2
    simp only [Finset.sum_add_distrib, Finset.sum_comm (f := fun a b ↦ ‖Z b a‖ ^ 2),
      Finset.sum_comm (f := fun a b ↦ p.1 b a ^ 2),
      Finset.sum_comm (f := fun a b ↦ p.2 b a ^ 2)] at h_sum
    linarith
  have hK' : Measurable fun p : Matrix n n ℝ × Matrix n n ℝ ↦ K (skewAddHerm p) :=
    hK.comp skewAddHerm.toLinearMap.continuous_of_finiteDimensional.measurable
  have h_subst : ∫⁻ Z : Matrix n n ℂ, K Z = ∫⁻ p, K (skewAddHerm (T₁.prodMap T₂ p)) :=
    (h_iso.lintegral_comp hK).symm
  simp [h_subst, lintegral_eq_abs_det_mul_comp volume h_ne hK', h_det, ENNReal.ofReal_pow,
    ← mul_assoc, ENNReal.inv_mul_cancel]

/-- Lebesgue measure on the complex matrices `Z = S + T / 2` of size `n`, with `S = skewOfReal s`
skew-hermitian and `T = hermOfReal t` hermitian, is `2 ^ (-n) ds dt`. -/
theorem lintegral_eq_skewOfReal_add_hermOfReal {K : Matrix n n ℂ → ℝ≥0∞} (hK : Measurable K) :
    ∫⁻ Z : Matrix n n ℂ, K Z =
      (2 ^ card n)⁻¹ * ∫⁻ t : Matrix n n ℝ, ∫⁻ s : Matrix n n ℝ,
        K (skewOfReal s + (2⁻¹ : ℂ) • hermOfReal t) := by
  rw [lintegral_eq_comp_skewAddHerm hK, volume_eq_prod, lintegral_prod]
  · simp only [skewAddHerm_apply]
  · exact (hK.comp skewAddHerm.toLinearMap.continuous_of_finiteDimensional.measurable).aemeasurable

/-! ### Blocks -/

/-- A hermitian matrix of size `n₁ + n₂` is given by its two diagonal blocks, which are hermitian,
and by one block off the diagonal. In the real coordinates `t`, for which the matrix itself is
`hermOfReal t`, this change of variables preserves volume. -/
theorem exists_measurePreserving_hermBlocks [Fintype n₁] [Fintype n₂] [DecidableEq n₁]
    [DecidableEq n₂] (e : n₁ ⊕ n₂ ≃ n) :
    ∃ φ : Matrix n n ℝ ≃ₜ Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ,
      MeasurePreserving φ ∧
      ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        (hermOfReal t).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr),
        t.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr)) := by
  -- The map is a linear isometry between Euclidean spaces of the same dimension.
  let f : Matrix n n ℝ →ₗ[ℝ] Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ :=
    { toFun t := (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        (hermOfReal t).submatrix (e ∘ Sum.inl) (e ∘ Sum.inr),
        t.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))
      map_add' := by simp [hermOfReal, submatrix_add]
      map_smul' := by simp [hermOfReal, submatrix_smul, submatrix_neg, smul_comm I] }
  have h_entry (t : Matrix n n ℝ) (a : n₁) (b : n₂) :
      ‖hermOfReal t (e (.inl a)) (e (.inr b))‖ ^ 2 =
        t (e (.inl a)) (e (.inr b)) ^ 2 + t (e (.inr b)) (e (.inl a)) ^ 2 := by
    simp [hermOfReal, skewOfReal, div_pow, RCLike.norm_sq_eq_def]
    ring
  have h_norm (t : Matrix n n ℝ) :
      ∑ a : n₁, ∑ b : n₁, t (e (.inl a)) (e (.inl b)) ^ 2 +
        (∑ a : n₁, ∑ b : n₂, ‖hermOfReal t (e (.inl a)) (e (.inr b))‖ ^ 2 +
          ∑ a : n₂, ∑ b : n₂, t (e (.inr a)) (e (.inr b)) ^ 2) =
        ∑ a : n, ∑ b : n, t a b ^ 2 := by
    simp only [h_entry, ← e.sum_comp, Fintype.sum_sum_type, Finset.sum_add_distrib]
    rw [Finset.sum_comm (s := (Finset.univ : Finset n₂)) (t := (Finset.univ : Finset n₁))]
    ring
  have h_rank : Module.finrank ℝ (Matrix n n ℝ) =
      Module.finrank ℝ (Matrix n₁ n₁ ℝ × Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ) := by
    simp [Module.finrank_matrix, ← card_congr e]
    ring
  -- The instances for the triple product are found once those for its last two factors are known.
  have : IsAddHaarMeasure (volume : Measure (Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ)) :=
    prod.instIsAddHaarMeasure _ _
  have : BorelSpace (Matrix n₁ n₂ ℂ × Matrix n₂ n₂ ℝ) := Prod.borelSpace
  obtain ⟨φ, hφ, hφ_symm⟩ := HasGaussianIntegral.exists_measurePreserving_equiv f h_norm h_rank
  exact ⟨φ.symm.toContinuousLinearEquiv.toHomeomorph,
    hφ.symm φ.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv, congrFun hφ_symm⟩

end Hermitian

/-- A hermitian matrix `hermOfReal t` of size `n₁ + 1`, with the extra index placed by `e`, is given
by a hermitian block of size `n₁`, by the rest of the column at the extra index and by the real
diagonal entry there. In the real coordinates `t` this change of variables preserves volume. -/
theorem exists_measurePreserving_hermCorner [Fintype n] [Fintype n₁] [DecidableEq n]
    [DecidableEq n₁] (e : n₁ ⊕ Unit ≃ n) :
    ∃ φ : Matrix n n ℝ ≃ₜ Matrix n₁ n₁ ℝ × (n₁ → ℂ) × ℝ,
      MeasurePreserving φ ∧
      ∀ t : Matrix n n ℝ, φ t = (t.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl),
        fun a : n₁ ↦ hermOfReal t (e (.inl a)) (e (.inr ())), t (e (.inr ())) (e (.inr ()))) := by
  obtain ⟨φ, φ_vol, φ_apply⟩ := exists_measurePreserving_hermBlocks e
  refine ⟨φ.trans ((Homeomorph.refl _).prodCongr (toCorner n₁).symm), ((MeasurePreserving.id _).prod
    (measurePreserving_toCorner.symm (toCorner n₁).toMeasurableEquiv)).comp φ_vol, fun t ↦ ?_⟩
  simp [φ_apply, toCorner_symm_apply]

end New

end
